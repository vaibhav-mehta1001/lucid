(* helpers for merging tables *)
[@@@ocaml.warning "-17-8-27"]

open Format
open LLSyntax
open MiscUtils
open DFSyntax
module RS = RuleSolve
open DebugPrint
open MiscUtils

(* logging *)
module DBG = BackendLogging

let outc = ref None
let dprint_endline = ref DBG.no_printf

(* enable logging for this module. *)
let start_logging () = DBG.start_mlog __FILE__ outc dprint_endline

let log_rules rules =
  CL.iter (fun r -> DBG.printf outc "%s\n" (dbgstr_of_rule r)) rules
;;

let oids_and_next_tids_of_rule cid_decls r =
  match r with
  | Match (_, _, acn_id) ->
    let acn = Cid.lookup cid_decls acn_id in
    let (Action (_, oids, next_tids)) = acn in
    oids, next_tids
  | OffPath _ -> [], []
;;

let is_offpath r =
  match r with
  | Match _ -> false
  | OffPath _ -> true
;;

(* extend a pattern so that it has a column for every var in vars *)
let extend_pat (vars : mid list) (pat : pattern) : pattern =
  let conds =
    CL.map (fun v -> Caml.Option.value (Cid.lookup_opt pat v) ~default:Any) vars
  in
  CL.combine vars conds
;;

(* make sure that a_pat and b_pat both have the same columns in the same order *)
let normalize_patterns a_pat b_pat =
  let a_vars, _ = CL.split a_pat in
  let b_vars, _ = CL.split b_pat in
  let vars = unique_list_of (a_vars @ b_vars) in
  let a_pat = extend_pat vars a_pat in
  let b_pat = extend_pat vars b_pat in
  a_pat, b_pat
;;

(* make sure that all rules in table t have the same columns in the same order *)
let normalize_table_patterns t =
  let (Table (t_id, rules, stg_opt)) = t in
  let vars = match_vars_of_rules rules in
  let rules =
    CL.map
      (fun r ->
        match r with
        | Match (r_id, pat, a_id) -> Match (r_id, extend_pat vars pat, a_id)
        | OffPath pat -> OffPath (extend_pat vars pat))
      rules
  in
  Table (t_id, rules, stg_opt)
;;

(* make sure two tables both have the same columns *)
let normalize_table_pair s t =
  let (Table (s_id, s_rules, s_stg_opt)) = s in
  let (Table (t_id, t_rules, t_stg_opt)) = t in
  let vars = match_vars_of_rules (s_rules @ t_rules) in
  let s_rules =
    CL.map
      (fun r ->
        match r with
        | Match (r_id, pat, a_id) -> Match (r_id, extend_pat vars pat, a_id)
        | OffPath pat -> OffPath (extend_pat vars pat))
      s_rules
  in
  let t_rules =
    CL.map
      (fun r ->
        match r with
        | Match (r_id, pat, a_id) -> Match (r_id, extend_pat vars pat, a_id)
        | OffPath pat -> OffPath (extend_pat vars pat))
      t_rules
  in
  Table (s_id, s_rules, s_stg_opt), Table (t_id, t_rules, t_stg_opt)
;;

(**** intersection of patterns ****)
(* find the intersection of two conditions (columns) in a match pattern, if it exists *)
let intersect_conditions (a_cond : condition) (b_cond : condition)
    : condition option
  =
  match a_cond with
  | Any -> Some b_cond (* a is wildcard, just b*)
  | Exact a_const ->
    (match b_cond with
    | Any -> Some a_cond (* b is wildcard, return a*)
    | Exact b_const ->
      if (* a and b are constants, if they're the same, return either. 
			   if they're not the same, there is no intersection in this dimension. *)
         a_const = b_const
      then Some a_cond
      else None)
;;

(* find the intersection of patterns a and b *)
let intersect_patterns (a_pat : pattern) (b_pat : pattern) : pattern option =
  let a_pat, b_pat = normalize_patterns a_pat b_pat in
  let vars, _ = CL.split a_pat in
  (* get the intersection conditions *)
  let _, a_conds = CL.split a_pat in
  let _, b_conds = CL.split b_pat in
  let ab_conds = CL.combine a_conds b_conds in
  let ab_conds =
    CL.map (fun (a_cond, b_cond) -> intersect_conditions a_cond b_cond) ab_conds
  in
  let has_intersect =
    CL.fold_left
      (fun intersect_exists cond_opt ->
        match cond_opt with
        | None -> false
        | Some _ -> intersect_exists)
      true
      ab_conds
  in
  match has_intersect with
  (* if there's an intersection, return it *)
  | true -> Some (CL.combine vars (CL.map Option.get ab_conds))
  (* *)
  | false -> None
;;

(* generate the rule that is the intersection of 
	s_rule : s and t_rule : t, assuming that s and t are parallel tables *)
(* if both rules are offpath, the intersection is offpath. 
	   if one rule is on path, the intersection is onpath *)
let gen_intersect_rule s_rule t_rule union_aid =
  let s_pat = pat_of_rule s_rule in
  let t_pat = pat_of_rule t_rule in
  let st_pat = Option.get (intersect_patterns s_pat t_pat) in
  DBG.printf outc "\t\tintersect rule pat: %s\n" (dbgstr_of_pat st_pat);
  let st_rid = Cid.fresh ["r"] in
  let intersect_rule =
    match union_aid with
    | None -> OffPath st_pat (* none means that the intersect rule is offpath*)
    | Some union_aid -> Match (st_rid, st_pat, union_aid)
  in
  intersect_rule
;;

(* for sequential intersection, we know that s_rule is on path 
	(to pass st feasibility check)
	but t_rule may or may not be on path. If its not, 
    we need to add an offpath rule. 
*)

type union_acn_request =
  | Parallel of oid option * rule * rule
  | Sequential of oid option * rule * rule

(* generate a reminder to add a new union action *)

let par_gen_union_acn_request_custom name_fcn s_rule t_rule =
  let s_aid = aid_of_rule s_rule in
  let t_aid = aid_of_rule t_rule in
  match is_offpath s_rule with
  | true ->
    (match is_offpath t_rule with
    (* both offpath -- there is no union rule. *)
    | true -> None, Parallel (None, s_rule, t_rule)
    (* s is offpath -- the union rule is t, which already exists, so there's no request to create *)
    | false -> Some t_aid, Parallel (None, s_rule, t_rule))
  | false ->
    (match is_offpath t_rule with
    (* t is offpath -- the union rule is s, which already exists *)
    | true -> Some s_aid, Parallel (None, s_rule, t_rule)
    (* both are onpath. The union rule is the union of s and t and it must be created. *)
    | false ->
      let new_aid = name_fcn s_aid t_aid in
      Some new_aid, Parallel (Some new_aid, s_rule, t_rule))
;;

let par_gen_union_acn_request = par_gen_union_acn_request_custom Cid.concat

(* for sequential merging, either rule being offpath means 
that the whole s, t sequence is offpath. *)
let seq_gen_union_acn_request_custom name_fcn s_rule t_rule =
  let s_aid = aid_of_rule s_rule in
  let t_aid = aid_of_rule t_rule in
  let new_aid = name_fcn s_aid t_aid in
  (* if either rules are offpath, the intersect rule is off path and there's no union action *)
  match is_offpath s_rule || is_offpath t_rule with
  | true -> None, Sequential (None, s_rule, t_rule)
  | false -> Some new_aid, Sequential (Some new_aid, s_rule, t_rule)
;;

let seq_gen_union_acn_request = seq_gen_union_acn_request_custom Cid.concat

(* generate a union action for parallel merging from two rules (s and t).
	the union action calls all the objects and next tables from either action. 
	assumption: at least one of s and t is on path. if not, there should never be a request to make a union rule *)
let gen_union_acn t_tid cid_decls new_acn_request =
  let new_acn_id, s_rule, t_rule =
    match new_acn_request with
    | Parallel (new_acn_id, s_rule, t_rule) -> new_acn_id, s_rule, t_rule
    | Sequential (new_acn_id, s_rule, t_rule) -> new_acn_id, s_rule, t_rule
  in
  match new_acn_id with
  | None -> cid_decls
  | Some new_acn_id ->
    (match Cid.exists cid_decls new_acn_id with
    | true -> cid_decls
    | false ->
      if is_offpath s_rule && is_offpath t_rule
      then
        error
          "Trying to generate a union action from two offpath rules. This \
           should not happen. ";
      let s_aid = aid_of_rule s_rule in
      let t_aid = aid_of_rule t_rule in
      let s_oids, s_next_tids = oids_and_next_tids_of_rule cid_decls s_rule in
      let t_oids, t_next_tids = oids_and_next_tids_of_rule cid_decls t_rule in
      let next_tids =
        match new_acn_request with
        | Parallel _ -> s_next_tids @ t_next_tids
        | Sequential _ -> t_next_tids
      in
      (* make sure that none of the actions point to t -- this can occur in a parallel merge. *)
      let next_tids =
        CL.filter (fun next_tid -> not (Cid.equals t_tid next_tid)) next_tids
      in
      DBG.printf
        outc
        "[gen_union_acn] new_acn_id=%s s_aid=%s t_aid=%s\n"
        (P4tPrint.str_of_private_oid new_acn_id)
        (P4tPrint.str_of_private_oid s_aid)
        (P4tPrint.str_of_private_oid t_aid);
      let new_acn =
        Action (new_acn_id, unique_list_of (s_oids @ t_oids), next_tids)
      in
      (new_acn_id, new_acn) :: cid_decls)
;;

(************ parallel merging *************)

(* 
new merging algorithm:

start with the rules in s
one at a time, merge in rules from t

for each rule in t:
	for each rule in s:
		- if (s is an added rule): do nothing
		- if (s^t is not feasible): do nothing
		- if (s^t is feasible and s^t covers s): replace s with s^t, note s^t as an added rule
		- if (s^t is feasible and s^t does not cover s): add s^t before s, note s^t as an added rule
	- if t is feasible given the current rules in s, add it to the end 

for sequential merging, we need two changes: 
	1. the last step doesn't happen -- t can only get executed through a rule from s
	2. the feasibility check changes -- s must have table(t) as one of its successor tables

*)

(* merge a rule from t with a rule from s, produce 0, 1, or 2 rules *)
let merge_t_into_s
    gen_union_acn_request
    st_feas_checker
    t_rule
    (new_action_requests, t_derived_s_rules, new_s_rules_so_far)
    s_rule
  =
  DBG.printf
    outc
    "[merge_t_into_s] attempting to merge\n\
     [merge_t_into_s] s_rule: %s\n\
     [merge_t_into_s] t_rule: %s \n"
    (dbgstr_of_rule s_rule)
    (dbgstr_of_rule t_rule);
  (* if s_rule is derived from t, we can't merge t_rule into s_rule *)
  let s_is_t_derived = CL.mem s_rule t_derived_s_rules in
  let more_new_action_requests, more_t_derived_s_rules, more_new_s_rules =
    match s_is_t_derived with
    | true ->
      [], [], [s_rule]
      (* s is derived from a higher priority rule in t (which is mutually exclusive with r_rule) *)
    | false ->
      let st_feas = st_feas_checker s_rule t_rule in
      (* s and t for parallel tables, s then t for sequential tables *)
      (match st_feas with
      | false -> [], [], [s_rule] (* nothing can match both s and t *)
      | true ->
        (* at this point, we are definitely adding an intersect rule (st) -- but we may not keep s. *)
        let union_aid, gen_acn_req = gen_union_acn_request s_rule t_rule in
        let intersect_rule = gen_intersect_rule s_rule t_rule union_aid in
        let s_is_reachable_after_s_t =
          RS.is_r_still_feasible s_rule [s_rule; t_rule]
        in
        (* QUESTION: do we also need to check whether s is feasible with respect to other new_s_rules_so_far? *)
        (match s_is_reachable_after_s_t with
        | false ->
          (* s_and_t covers s, so we want to add only s_and_t, which is derived from t. *)
          DBG.printf
            outc
            "\t[merge_t_into_s]deleting: %s\n"
            (dbgstr_of_rule s_rule);
          DBG.printf
            outc
            "\t[merge_t_into_s]adding: %s\n"
            (dbgstr_of_rule intersect_rule);
          [gen_acn_req], [intersect_rule], [intersect_rule]
        | true ->
          (* s_and_t does not cover s, so we want to add s_and_t, then s. *)
          DBG.printf
            outc
            "\t[merge_t_into_s]adding: %s\n"
            (dbgstr_of_rule intersect_rule);
          DBG.printf
            outc
            "\t[merge_t_into_s]adding: %s\n"
            (dbgstr_of_rule s_rule);
          [gen_acn_req], [intersect_rule], [intersect_rule; s_rule]))
  in
  DBG.printf outc "\n[merge_t_into_s] ---- new_s_rules ----\n";
  log_rules more_new_s_rules;
  DBG.printf outc "\n[merge_t_into_s] ---- end new_s_rules ----\n\n";
  let out_tup =
    ( new_action_requests @ more_new_action_requests
    , t_derived_s_rules @ more_t_derived_s_rules
    , new_s_rules_so_far @ more_new_s_rules )
  in
  out_tup
;;

(* merge a rule from t into all the rules in s *)
let merge_t_into_all_s
    gen_union_acn_request
    st_feas_checker
    t_only_feas_checker
    (new_action_requests, t_derived_s_rules, s_rules)
    t_rule
  =
  (* merge t into each s rule *)
  DBG.printf outc "\n[merge_t_into_all_s] START\n";
  DBG.printf outc "\tt_rule:\n%s\n\ts_rules:\n" (dbgstr_of_rule t_rule);
  log_rules s_rules;
  DBG.printf outc "\n--------\n";
  let new_action_requests, updated_t_derived_s_rules, updated_s_rules =
    CL.fold_left
      (merge_t_into_s gen_union_acn_request st_feas_checker t_rule)
      (new_action_requests, t_derived_s_rules, [])
      s_rules
  in
  (* if we can reach t without going through a rule in s, we need to add t to the end of the new rule set. *)
  let updated_t_derived_s_rules, updated_s_rules =
    match t_only_feas_checker updated_s_rules t_rule with
    | true -> updated_t_derived_s_rules @ [t_rule], updated_s_rules @ [t_rule]
    | false -> updated_t_derived_s_rules, updated_s_rules
  in
  DBG.printf
    outc
    "\n[merge_t_into_all_s]\n\tt_rule:\n%s\n\tUPDATED s_rules:\n"
    (dbgstr_of_rule t_rule);
  log_rules updated_s_rules;
  DBG.printf outc "\n--------\n";
  (* filter out any unreachable rules *)
  let num_rules = CL.length updated_s_rules in
  let updated_s_rules = unique_list_of updated_s_rules in
  let updated_s_rules =
    CL.filter (RS.is_reachable_in_order updated_s_rules) updated_s_rules
  in
  let num_reachable_rules = CL.length updated_s_rules in
  DBG.printf
    outc
    "[merge_t_into_all_s] filtered out %i unreachable rules\n"
    (num_rules - num_reachable_rules);
  DBG.printf outc "[merge_t_into_all_s] reachable rules: \n";
  log_rules updated_s_rules;
  DBG.printf outc "\n[merge_t_into_all_s] END\n";
  new_action_requests, updated_t_derived_s_rules, updated_s_rules
;;

(* merge each rule from t rules into the list of rules s_rules 
return the final rules and any newly generated actions *)
let merge_all_t_into_all_s
    gen_union_acn_request
    st_feas_checker
    t_only_feas_checker
    s_rules
    t_rules
  =
  let new_action_requests, all_t_derived_s_rules, final_s_rules =
    CL.fold_left
      (merge_t_into_all_s
         gen_union_acn_request
         st_feas_checker
         t_only_feas_checker)
      ([], [], s_rules)
      t_rules
  in
  let _ = all_t_derived_s_rules in
  (* don't need to return this *)
  final_s_rules, new_action_requests
;;

(* merge function that can implement either parallel or sequential table merging, 
   based on checker functions passed in *)
let merge_tables
    gen_union_acn_request
    check_st_feas
    check_t_only_feas
    cid_decls
    s_tid
    t_tid
  =
  !dprint_endline "---- [merge tables] ----";
  !dprint_endline
    (DebugPrint.str_of_decls
       [Cid.lookup cid_decls s_tid; Cid.lookup cid_decls t_tid]);
  !dprint_endline "---- [merge tables] ----";
  let [s; t] = CL.map (Cid.lookup cid_decls) [s_tid; t_tid] in
  let (Table (s_id, s_rules, s_stage)) = s in
  let (Table (t_id, t_rules, t_stage)) = t in
  (* normalize the patterns of both tables -- will this help the invalid merging of table groups? *)
  let s, t = normalize_table_pair s t in
  let cid_decls = Cid.replace cid_decls s_id s in
  let cid_decls = Cid.replace cid_decls t_id t in
  let orig_t_aids = aids_of_tid cid_decls t_tid in
  let orig_s_aids = aids_of_tid cid_decls s_tid in
  (* find s_actions -- need to know them for a sequential merge *)

  (* log_prog cid_decls; *)
  let s_acns_map = acn_map_of_tid cid_decls s_id in
  (* merge and generate new actions *)
  let merged_s_rules, new_action_requests =
    (merge_all_t_into_all_s
       gen_union_acn_request
       (check_st_feas s_acns_map t)
       check_t_only_feas)
      s_rules
      t_rules
  in
  (* generate new actions and add them to cid decls*)
  let cid_decls =
    CL.fold_left
      (gen_union_acn t_id)
      cid_decls
      (unique_list_of new_action_requests)
  in
  (* generate s with new rules *)
  let new_s = Table (s_id, merged_s_rules, s_stage) in
  DBG.printf
    outc
    "[merge_tables] finished merging into table %s -- new table has %i rules\n"
    (P4tPrint.str_of_private_oid s_id)
    (CL.length merged_s_rules);
  log_rules merged_s_rules;
  (* normalize patterns in s *)
  let new_s = normalize_table_patterns new_s in
  (* update s in cid_decls *)
  let cid_decls = Cid.replace cid_decls s_id new_s in
  (* remove t from cid_decls *)
  let cid_decls = Cid.remove cid_decls t_id in
  (* delete any actions from t that are no longer used *)
  let new_st_aids = aids_of_tid cid_decls s_id in
  (* let used_in_st = CL.filter (fun orig_aid -> CL.mem orig_aid new_st_aids) (orig_t_aids@orig_s_aids) in  *)
  let unused_in_st =
    CL.filter
      (fun orig_aid -> not (CL.mem orig_aid new_st_aids))
      (orig_t_aids @ orig_s_aids)
  in
  (*[packetin~0, merged_acn~1] *)
  let cid_decls =
    CL.fold_left
      (fun cid_decls unused_aid -> Cid.remove cid_decls unused_aid)
      cid_decls
      unused_in_st
  in
  (* log_prog cid_decls; *)
  (* return updated cid_decls *)
  cid_decls
;;

(**** feasibility checkers that differ depending on whether its a parallel or sequential merge ****)
(* can you execute an action in t without first executing an action in s? *)
(* for a parallel table, you can get to the t_rule if ![st_rules] and t_rule is true *)
let par_t_only_feas st_rules t_rule = RS.is_r_still_feasible t_rule st_rules

(* for a sequential table, its impossible because some s rule must direct you to t.*)
let seq_t_only_feas st_rules t_rule =
  let _, _ = st_rules, t_rule in
  false
;;

(* is it possible to execute s_rule and t_rule? *)
let par_st_feas s_acns_map t s_rule t_rule =
  let _, _ = s_acns_map, t in
  RS.is_intersection_feasible s_rule t_rule
;;

(* QUESTION: do we need to check the higher priority rules in t, for the intersect feasibility? *)

(* 
	is it possible to execute s_rule, then execute t_rule? 
	if s_rule is off path, then it is not possible. 
*)
let seq_st_feas s_acns_map t s_rule t_rule =
  match s_rule with
  | OffPath _ ->
    false (* if s is offpath, then there's no way we can ever get to t. *)
  | Match (_, _, s_acn_id) ->
    DBG.printf
      outc
      "seq_st_feas: s_acn_id = %s\n"
      (P4tPrint.str_of_private_oid s_acn_id);
    let tids_called_from_s_rule = succs_of_aid s_acns_map s_acn_id in
    (match RS.is_intersection_feasible s_rule t_rule with
    (* the intersection must be feasible *)
    | false -> false
    | true ->
      (* the action called by s_rule must have table t as a successor. *)
      CL.mem (tid_of_tbl t) tids_called_from_s_rule)
;;

(**** main parallel and sequential merge functions ****)

(* merge two parallel tables, return updated cid_decls with new s_tid *)
let parallel_merge (cid_decls : declsMap) s_tid t_tid =
  DBG.printf
    outc
    "---PARALLEL MERGE: tables %s and %s---\n"
    (P4tPrint.str_of_private_oid s_tid)
    (P4tPrint.str_of_private_oid t_tid);
  merge_tables
    par_gen_union_acn_request
    par_st_feas
    par_t_only_feas
    cid_decls
    s_tid
    t_tid
;;

(* merge two sequential tables, return updated cid_decls with new s_tid *)
let sequential_merge (cid_decls : declsMap) s_tid t_tid =
  DBG.printf
    outc
    "---SEQUENTIAL MERGE: tables %s and %s---\n"
    (P4tPrint.str_of_private_oid s_tid)
    (P4tPrint.str_of_private_oid t_tid);
  merge_tables
    seq_gen_union_acn_request
    seq_st_feas
    seq_t_only_feas
    cid_decls
    s_tid
    t_tid
;;

(**** sequential condition propagation ****)

(* copy a rule in s, to build the table s'. When we do merge s' t, we want a table with the actions of t, but the path constraints of st.
	If the rule's action doesn't go to table t, replace the rule with an offpath. 
		- this means that the rule can never execute in the new t, because s will never goto t if these constraints are satisfied. 
		- if slicing was done correctly, the rule should already _be_ an offpath in this case.
	If the rule's action does go to t, replace the rule with an empty action 
	(because in the merged table we only want to execute the instructions from t).
*)
let null_action_copy_of_rule cid_decls t_id r =
  match r with
  | Match (r_id, pat, acn_id) ->
    let succ_tids = succs_of_aid cid_decls acn_id in
    (match CL.mem t_id succ_tids with
    | true ->
      (* the rule goes to t -- this is a viable execution that should call nothing from table s.*)
      let new_acn_id = Cid.concat (Cid.fresh [""]) acn_id in
      (* let new_acn_id = Cid.concat acn_id (Cid.fresh ["copy"]) in  *)
      let new_acn = Action (new_acn_id, [], succs_of_aid cid_decls acn_id) in
      let new_r_id = Cid.concat (Cid.fresh [""]) r_id in
      (* let new_r_id = Cid.concat r_id (Cid.fresh ["copy"]) in  *)
      let new_rule = Match (new_r_id, pat, new_acn_id) in
      new_rule, [new_acn]
    | false ->
      (* the rule does not goes to t -- this is not a viable execution. executing this rule in the constrained table t should be impossible. *)
      let new_rule = OffPath pat in
      new_rule, [])
  | OffPath _ -> r, []
;;

let add_acn_to_map cid_decls acn =
  match acn with
  | Action (aid, oids, tids) -> cid_decls @ [aid, acn]
  | _ -> error "not an action"
;;

(* make a copy of the table s_tid, with all actions that go to t set to no-op, and all actions that 
don't go to t set to offpaths. *)
let null_action_copy_of_s_tid cid_decls s_tid t_tid =
  let s = Cid.lookup cid_decls s_tid in
  match s with
  | Table (tbl_id, rules, stage_opt) ->
    (* generate copies of all rules and the new null actions  *)
    let new_rules, new_null_actions_lists =
      CL.split (CL.map (null_action_copy_of_rule cid_decls t_tid) rules)
    in
    let new_null_actions = CL.flatten new_null_actions_lists in
    (* add new rules to cid_decls *)
    let cid_decls = CL.fold_left add_acn_to_map cid_decls new_null_actions in
    (* generate the null table copy *)
    let new_tbl_id = Cid.concat tbl_id (Cid.fresh ["noop_pred"]) in
    let new_tbl = Table (new_tbl_id, new_rules, stage_opt) in
    (* add the table to cid_decls *)
    let cid_decls = cid_decls @ [new_tbl_id, new_tbl] in
    (* return the no-op table id and the updated cid_decls *)
    cid_decls, new_tbl_id
  | _ ->
    error
      (sprintf "couldn't find table: %s\n" (P4tPrint.str_of_private_oid s_tid))
;;

(* change the name of a table to new_tid and update the entry for new_tid in the datastruct *)
let rename_and_update cid_decls new_tid tbl =
  (* set the name of new_tbl = new_tid *)
  let old_tid = tid_of_tbl tbl in
  let renamed_tbl = rename_tbl new_tid tbl in
  let new_cid_decls = Cid.remove cid_decls old_tid in
  let new_cid_decls = new_cid_decls @ [new_tid, renamed_tbl] in
  new_cid_decls
;;

let propagate_condition (cid_decls : declsMap) s_tid t_tid =
  DBG.printf
    outc
    "[propagate conditions] table %s to table %s---\n"
    (P4tPrint.str_of_private_oid s_tid)
    (P4tPrint.str_of_private_oid t_tid);
  (* make a copy of the data structure, with table s_tid having actions replaced by null actions *)
  let noop_s_cid_decls, noop_s_tid =
    null_action_copy_of_s_tid cid_decls s_tid t_tid
  in
  (* merge the tables into st_tid *)
  let noop_s_cid_decls = sequential_merge noop_s_cid_decls noop_s_tid t_tid in
  (* get the st table *)
  let noop_st = Cid.lookup noop_s_cid_decls noop_s_tid in
  (* remove the st' table, add the t table back in. The s table should still be there, because we only operated on a copy. *)
  let updated_cid_decls = rename_and_update noop_s_cid_decls t_tid noop_st in
  (* return the new data structure *)
  updated_cid_decls
;;

type propagation_type =
  | AllMustMatch (* table t executes if all of its conditions hold. *)
  | OneMustMatch

(* table t executes if any of its conditions hold. *)

let propagate_condition_generic prop_type cid_decls s_tid t_tid =
  LLValidate.validate_cid_decls
    cid_decls
    "[propagate_condition_generic] start";
  (* make a copy of the data structure, with table s_tid having actions replaced by null actions *)
  let noop_s_cid_decls, noop_s_tid =
    null_action_copy_of_s_tid cid_decls s_tid t_tid
  in
  DBG.printf
    outc
    "[propagate_condition_generic] table %s (noop copy: %s) to table %s\n"
    (P4tPrint.str_of_private_oid s_tid)
    (P4tPrint.str_of_private_oid noop_s_tid)
    (P4tPrint.str_of_private_oid t_tid);
  (* merge the tables into st_tid *)
  let merge_name_fn _ b = b in
  (* let merge_name_fn = Cid.concat in  *)
  let noop_s_cid_decls =
    match prop_type with
    | AllMustMatch ->
      DBG.printf outc "[propagate_condition_generic] AllMustMatch\n";
      (*sequential merge, with different union acton name function*)
      merge_tables
        (seq_gen_union_acn_request_custom merge_name_fn)
        seq_st_feas
        seq_t_only_feas
        noop_s_cid_decls
        noop_s_tid
        t_tid
    | OneMustMatch ->
      DBG.printf outc "[propagate_condition_generic] OneMustMatch\n";
      (*parallel merge, with different union action name function*)
      merge_tables
        (par_gen_union_acn_request_custom merge_name_fn)
        par_st_feas
        par_t_only_feas
        noop_s_cid_decls
        noop_s_tid
        t_tid
  in
  (* get the st table *)
  let noop_st = Cid.lookup noop_s_cid_decls noop_s_tid in
  (* remove the st' table, add the t table back in. The s table should still be there, because we only operated on a copy. *)
  let updated_cid_decls = rename_and_update noop_s_cid_decls t_tid noop_st in
  (* return the new data structure *)
  LLValidate.validate_cid_decls
    updated_cid_decls
    "[propagate_condition_generic] end";
  updated_cid_decls
;;

let preds_tid_ctr = ref 0

let next () =
  preds_tid_ctr := !preds_tid_ctr + 1;
  !preds_tid_ctr
;;

let fresh_preds_tbl cid_decls : oid * declsMap =
  let merged_id = next () in
  let tbl_id = Cid.create_ids [Id.to_id ("merged_preds_tbl", merged_id)] in
  let acn_id = Cid.create_ids [Id.to_id ("merged_preds_acn", merged_id)] in
  let acn = Action (acn_id, [], []) in
  (* a rule to do nothing for any packet.*)
  let def_rule = Match (Cid.fresh ["r"], [], acn_id) in
  let tbl = Table (tbl_id, [def_rule], None) in
  tbl_id, cid_decls @ [acn_id, acn; tbl_id, tbl]
;;

(* 
propagate all the conditions from a set of predecessors (s_tid) to 
a table (t_tid). The new t_tid's rules should enforce all the conditions 
that must be met for it to execute, given its predecessors s_tids.
*)
let merge_pred_conditions cid_decls s_tids t_tid =
  let orig_cid_decls = cid_decls in
  (* 1. make copies of s_tids, offpath the rules that don't lead to t_tid *)
  let fold_f t_tid (cid_decls, new_s_tids) s_tid =
    let cid_decls, new_s_tid =
      null_action_copy_of_s_tid cid_decls s_tid t_tid
    in
    cid_decls, new_s_tids @ [new_s_tid]
  in
  let cid_decls, s_copy_tids =
    CL.fold_left (fold_f t_tid) (cid_decls, []) s_tids
  in
  (* 2. parallel merge all the s_tids, to get a table with rules encoding all the ways control can flow 
	from any one of s_tids to t_tid *)
  let merge_pred_pair cid_decls a_tid b_tid =
    merge_tables
      (par_gen_union_acn_request_custom (fun _ b -> b))
      par_st_feas
      par_t_only_feas
      cid_decls
      a_tid
      b_tid
  in
  (* merge copies of s_tids into merged_pred_tid *)
  let merged_preds_tid, cid_decls = fresh_preds_tbl cid_decls in
  let fold_f merged_tid cid_decls next_pred =
    merge_pred_pair cid_decls merged_tid next_pred
  in
  let cid_decls =
    CL.fold_left (fold_f merged_preds_tid) cid_decls s_copy_tids
  in
  (* 3. propagate conditions from merged_preds_tid to t_tid *)
  let cid_decls =
    propagate_condition_generic AllMustMatch cid_decls merged_preds_tid t_tid
  in
  (* 4. get the new t_tid *)
  let new_t_tbl = Cid.lookup cid_decls t_tid in
  (* 5. replace t_tid in the original cid decls and return *)
  Cid.replace orig_cid_decls t_tid new_t_tbl
;;

(* test runs *)
let run_test test_name case_generator merge_fcn =
  DBG.printf outc "---------testing %s ---------\n" test_name;
  let s, t, decls_map = case_generator () in
  let decls_map_new = merge_fcn decls_map s t in
  let _ = decls_map_new in
  ()
;;

(* 
let test_merge_tables () = 
	(* run_test "parallel merge with simple table pair" gen_simple_table_ex parallel_merge; *)
 	run_test "sequential merge with nested if/else tables" gen_nested_if_tbl_ex sequential_merge;
 	(* run_test "parallel merge with nested if/else tables" gen_nested_if_tbl_ex parallel_merge; *)
	(* run_test "parallel merge with infeasible path" gen_infeasible_tup_ex parallel_merge; *)

 	exit 1

	(* test_nested_if_tables () *)
;;

let test_propagate_conditions () = 
 	run_test "sequential merge with nested if/else tables" gen_nested_if_tbl_ex sequential_merge;
 	DBG.printf outc "-------------\n";
	run_test "propagate conditions with nested if / else tables" gen_nested_if_tbl_ex propagate_condition;
;; *)