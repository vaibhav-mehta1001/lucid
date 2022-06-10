open Syntax
open SyntaxUtils
open Batteries
open Collections
open Printing

let print_keys keys = 
let _ = print_string "Printing Keys \n" in 
 List.map(fun (id,_)-> print_string ((fst id) ^ "\n")) keys 

let print_vals vals = 
 let _ = print_string "Printing Array Name \n" in 
 List.map(fun (i,(s,_))->
 let _ = print_int i in 
  print_string ((s) ^ "\n")) vals 
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)


let get_args_str args = List.map (fun x ->
match x.e with 
| EVar x ->  (Cid.to_string_name x)
| _ -> failwith "s") args

let rec firstk k xs = match xs with
| [] -> failwith "firstk"
| x::xs -> if k=1 then [x] else x::firstk (k-1) xs

let get_indices keys exprs = 
List.flatten (List.mapi (fun i s -> List.flatten(List.mapi(fun j s1 -> if String.equal (fst(fst s1)) s then [(j)] else 
 []) keys )) exprs ) 

let rec print_string_list ls = 
match ls with 
| [] -> print_string "done printing string\n" 
| hd :: tl -> let _ = print_string (hd) in let _ = print_string "\n" in 
print_string_list tl

let rec print_params ps = 
  match ps with 
  | [] -> print_string "Done with params\n"
  | hd :: tl -> let _ = print_string (fst(fst(hd))) in let _ = print_string "\n" 
  in print_params tl

(*
  Actual args should be that args of the table, table keys should be 
  params of the rule and expr_args is the one we're interested in resolving
*)
let resolve_order (actual_args : params) (table_keys : params) (expr_args) = 
      let expr_args = (firstk (List.length table_keys) expr_args) in 
      let _ = print_params table_keys in 
      let actual_args = firstk (List.length table_keys) actual_args in 
      let _ = print_string_list expr_args in 
      let _ = print_params actual_args in 
      let expr_args = get_indices table_keys expr_args in 
      let args = List.combine actual_args (expr_args)
      in let args = List.stable_sort (fun a b -> (snd a) - (snd b)) args
      in List.map(fun (a,_) -> a) args  

(* 
   match decl.d with 
   | DMin(n, DRule {lhs=Table{name; loc; args}; preds; _}) ->
    if (Id.equal_names rule n) then () else ()
   | _ -> [] *)


let get_pred table pred =
    match pred with 
    |Table{name;args=args} -> if Id.equal_names table name then args else []

let get_args_rule rule_name table (actual_args : params) 
rule_ctxt (table_ctxt : (Id.t * Syntax.params) list)
 name_to_rule =
    let table_keys = List.assoc rule_name rule_ctxt in 

   (* let table_keys = List.assoc table table_ctxt in  *)
   (* let actual_args = List.assoc rule_name rule_ctxt in  *)
   let rule =  List.assoc (fst(rule_name)) name_to_rule in 
    let preds = match rule with  
                    | DRule{lhs=lhs;preds;_} -> preds
                    | _ -> failwith "Non rule in ctxt" 
                    in 
  let expr_args = List.flatten (List.map (get_pred table) preds) in 
  resolve_order actual_args table_keys (get_args_str expr_args)

        
(*ID is table name *)
let rec generate_table_body id graphs params rule_ctxt table_ctxt rule_args_ctxt = 
 let generate_deps d = 
  List.map(fun name ->  let _ = print_string (fst(name)) in
              {s=SGen(GSingle(None),
              {e=ECall(Cid.create [(fst(name))], 
                     (List.map (fun x -> {e=EVar(Cid.create[ fst(fst(x))]);ety=None;espan=Span.default}) 
                     (get_args_rule name id params rule_args_ctxt table_ctxt rule_ctxt)))
                     ;ety=None;espan = Span.default});
                      sspan=Span.default}
                    ) d 
 in let deps = match (List.assoc_opt id graphs)
  with | Some dep -> dep (*dep is rule name *)
       | None -> [] in 
 let stmts = List.fold_left(fun acc x-> 
                  {s=SSeq(acc, x);sspan=Span.default}) {s=SNoop;sspan=Span.default} (generate_deps deps) in DHandler((("event_"^(fst(id))), snd(id)), (params,stmts))

let generate_val_tables_ctxt decl =
  match decl.d with 
  | DTable{name; loc; keys; value; merge} -> 
  let value = List.mapi (fun i x -> (i, ((gensym (fst(fst x))), (snd x)))) value in 
 [(name, value)]
  | _  -> []

let generate_array (idx, (name, ty)) =
   [DGlobal(Id.create((name)), {raw_ty=TName((Cid.create ["Array"; "t"]),
                          [IConst (32); ], true); teffect=FZero; tspan=Span.default; tprint_as=  ref None},
                           {e=ECall((Cid.create["Array" ;"create"]), [{e=EInt((Z.of_int 1024), None);ety=None;espan=Span.default}]);
                            ety=None; espan=Span.default})]

let generate_val_arrays name (ctxt : (Syntax.id * (int * (string * Syntax.ty)) list) list)  = 
   let value = List.assoc name ctxt in List.flatten (List.map generate_array value)


let generate_table graph (vals_ctxt)  rule_ctxt table_ctxt rule_args  d = match d.d with 
                         | DTable{name; loc; keys; value; merge} ->  let param = 
                         begin match loc with 
                         | Some v -> [(v, {raw_ty=(TInt(IConst 32));teffect=FZero;
                           tspan=Span.default;tprint_as= ref None})] 
                         | None -> [] end in 
                         let param = param @ keys @ value in 
                         (generate_val_arrays name vals_ctxt) @
                         [DEvent((("event_" ^ (fst name)), (snd name)), EEntry(true), [], param );
                          (generate_table_body name graph param rule_ctxt table_ctxt rule_args)]
                         | _ -> []


(* MAP from table name to keys  *)
let tbl_arg_ctxt (decls : decls) = 
  let helper d = List.fold_left (
    fun acc d -> match d.d with 
    | DTable{name; loc; keys; value; merge} ->  let param = 
                         begin match loc with 
                         | Some v -> [(v, {raw_ty=(TInt(IConst 32));teffect=FZero;
                           tspan=Span.default;tprint_as= ref None})] 
                         | None -> [] end in 
                         (name, param @ keys) :: acc
    
    | _ -> acc 
  
  ) d in helper [] decls


(*Map from rule name to rule args -- rule args are keys of first predicate  *) 
let generate_rule_param (table_ctxt) ctxt d = match d.d with 
   | DMin(n, DRule {lhs=Table{name; loc; args}; preds; _ }) -> 
    begin match (List.nth preds 0) with 
   | Table{name;args=args;_} ->  (n, List.assoc name table_ctxt) :: ctxt end 
   | _ -> ctxt


let rule_ctxt (decl : decls) = List.map (fun x ->  
    match x.d with
    | DRule {lhs=Table{name; loc; args};  _ } -> 
    DMin(((gensym ("rule_" ^ (fst name))),0), x.d)
    |_ -> x.d) decl


(*TOTAL 3 CTXTS : 
                  Name -> Rule
                  Name -> Args (where args is the input to the rule)
                  Table Name -> keys 
*)
let name_to_rule (decl : decls) = List.fold_left (fun acc x ->
   match x.d with
    | DMin((name, _), r) -> (name, r) :: acc 
    |_ -> acc) [] decl



(* 
   Build Dependency Graph  
   To Generate dependent events, do the following: 
   look up graph. For each edge, look up the rule_ctxt 
   using the NAME of the edge 
*)

let filter_preds table_key preds = 
  let max = List.fold_left 
  (fun (l : int) (Table{name;_}) -> let key = 
  List.length(List.assoc name table_key) in 
  if (key >= l) then key else l)  0 preds in 
  let keeps = List.filter(fun (Table{name;_}) -> 
   let key =  List.length(List.assoc name table_key) in key >= max) preds in 
   keeps 

let add_to_list assoc (name, Table{name=name2;_})= 
       match List.assoc_opt name assoc with 
                                    | Some v ->   (name2, (name) :: v) :: assoc
                                    | None ->  (name2, [name]) :: assoc

let add_to_graph  table_ctxt (graph) d = match d.d with 
                              | DMin(n, DRule {lhs=Table{name; loc; args}; preds; exps}) -> 
                              let preds = filter_preds table_ctxt preds in 
                              let t = List.map (fun x -> (n, x)) preds in 
                               List.fold add_to_list graph t 
                              | _ -> graph

let create_graph table_ctxt decls = List.fold (add_to_graph table_ctxt) [] decls

let create_rule_event rule_args d =   
match d.d with  
| DMin(n, DRule {lhs=Table{name; loc; args}; _ })-> 
   [DEvent((n), EEntry(true), [], List.assoc n rule_args)]                   
| _ -> [] 

let compile_lookup  (name : cid) arr_names i exp = 
  match exp.e with 
  | EVar x ->
    let _ = print_int i in 
   let arr_name = Id (fst(List.assoc i arr_names), 0)
  in SLocal(Cid.to_id x, 
   {raw_ty=(TInt(IConst 32));teffect=FZero; tspan=Span.default; tprint_as=ref None} , 
  {e=ECall((Cid.create["Array";"get"]), 
  [{e=EVar arr_name;ety=None;espan=Span.default};
  {e=EVar name;ety=None;espan=Span.default} ])
  ;ety=None;espan=Span.default})
  | _ -> failwith "bad arg"

let rec lastk ls k i = 
match ls with 
| [] -> []
| _ :: tl -> if i = k then tl else lastk tl k (i+1)

let compile_pred params vals_ctxt tbl_arg_ctxt pred  =
 match pred with
 | Table{name; loc; args} ->  let keys = List.assoc name tbl_arg_ctxt in
 let idx = ((gensym "idx"),0)
 in let prog = SLocal(idx, 
 {raw_ty=(TInt(IConst 16));teffect=FZero; tspan=Span.default; tprint_as=ref None} , 
  {e=EHash((IConst 16), (List.map (fun (id, _) -> 
  {e=EVar (Id id);ety=None;espan=Span.default}) 
  params)); ety=None; espan=Span.default}) in 
  let values = firstk  (List.length args - List.length keys) (List.rev args) in 
  let arr_names = List.assoc name vals_ctxt in 
  let _ = print_string "--- Printing pred stuff --- \n" in 
  let _ =  print_keys keys in 
  let _ = print_vals arr_names in 
  let _ = print_string "\n" in let _ = print_int (List.length values) in 
  let _  = print_string "\n printing args \n "  in 
  let _ = print_string_list (get_args_str args) in 

  prog :: (List.mapi (compile_lookup (Id idx) arr_names)) values 

let compile_exps (acc:e) (exp : exp) = 
 match acc with 
| EOp(op, exps) -> EOp(And, exp :: exps)                
| _ -> failwith "Only binary ops"

let compile_set (name : cid) arr_names i exp = 
  match exp.e with 
  | EVar x -> let arr_name = Id (fst(List.assoc i arr_names), 0)
  in SUnit(  
  {e=ECall((Cid.create["Array";"set"]), 
  [{e=EVar arr_name;ety=None;espan=Span.default};
  {e=EVar name;ety=None;espan=Span.default};
   {e=EVar x;ety=None;espan=Span.default}])
  ;ety=None;espan=Span.default})
  | _ -> failwith "bad arg"



let compile_true_branch keys args arr_names  = let idx = ((gensym "idx"),0)
 in let prog = SLocal(idx, 
 {raw_ty=(TInt(IConst 16));teffect=FZero; tspan=Span.default; tprint_as=ref None} , 
  {e=EHash((IConst 16), (List.map (fun (id) -> 
  {e=EVar (Id (id,0));ety=None;espan=Span.default}) 
  (firstk (List.length keys) (get_args_str args)))); ety=None; espan=Span.default}) in 
  let values = firstk (List.length args - List.length keys) (List.rev args) in 
  prog :: (List.mapi (compile_set (Id idx) arr_names) values)

let to_stmt s = 
 {s=s;sspan = Span.default}

let combine_stmt stmts = 
let f acc s = 
 match acc.s with 
 SSeq(_) -> to_stmt (SSeq(acc,s))
 | _ -> to_stmt (SSeq(s,to_stmt SNoop))
 in  (List.fold_left f (to_stmt SNoop) stmts)


(* Compile Body Event *)


let compile_handler_body vals_ctxt rule_args 
(tbl_arg_ctxt : (Syntax.id * (Syntax.id * Syntax.ty) list) list) rule = 
match rule.d with 
| DMin(n, DRule {lhs=Table{name; loc; args}; preds; exps}) -> 
 let keys = List.assoc name tbl_arg_ctxt in 
  let _ = print_keys keys in 
 let arr_names = List.assoc name vals_ctxt in 
 let _ = print_vals arr_names in 
 let params = List.assoc n rule_args in 
 let stmts = List.flatten (List.map(compile_pred params vals_ctxt tbl_arg_ctxt) preds)
 in let exps = if (List.length exps > 1) then 
  {e=(List.fold_left compile_exps (EOp(And, [])) exps);ety=None; espan=Span.default} else 
  (List.nth exps 0) 

in let b1 = compile_true_branch keys args arr_names in 
let stmts = (List.map to_stmt stmts) @ 
[to_stmt (SIf(exps, combine_stmt (List.map to_stmt b1), to_stmt SNoop))] in 
let body_stmt = combine_stmt stmts 
in [DHandler(n, (params,body_stmt))]
 
| _ -> []
(*  
| _ -> []
let create_handlers event_list = failwith "unimplemented" *)

let remove (decl : decls) : decls = 
                  let filter d  = match d.d with 
                                 | DRule _ ->  false
                                 | DTable _ -> false 
                                 | DMin(_) -> false
                                 | _ -> true
in  List.filter (filter) decl ;; 

let print_assoc assoc = List.map (fun (x,_) -> print_string ((fst x)^"\n")) assoc
let process_prog (decl : decls) : decls =
    let vals_ctxt = List.flatten (List.map generate_val_tables_ctxt decl) in 
    let decl = rule_ctxt decl in 
    let decl = List.map (fun x -> {d=x;dspan=Span.default}) decl in 
    let table_args = tbl_arg_ctxt decl in 
    let graph = create_graph table_args decl in 
    (* let rctxt = rule_ctxt decl in  *)
    let rule_args = List.fold_left (generate_rule_param table_args) [] decl in 
    let rule_mapping = name_to_rule decl in 
    let _ = print_assoc graph in 
    let _ = print_string "\n Graph DOne \n" in 
    let prog =  List.flatten (List.map (create_rule_event rule_args) decl) in
    let prog = prog @ List.flatten
     (List.map (generate_table graph  vals_ctxt rule_mapping table_args rule_args) decl) in 
    let prog = prog @ List.flatten (List.map (compile_handler_body vals_ctxt rule_args table_args) decl)
    in 
    (* let prog = prog @ List.flatten (List.map (create_rule_event pctxt) decl) *)
   let prog = List.map(fun x -> {d=x;dspan=Span.default}) prog
   
    in remove prog

