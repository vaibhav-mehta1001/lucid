open Syntax
open SyntaxUtils
open Batteries
open Collections
open Printing

let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)
(*
let option_wrapper opt = 
  match opt with |Some v -> v | None -> []

let get_base_facts decl = 
  let f  l d= match d.d with 
            | DBaseTable(name; _) -> name :: l
in List.fold_left f [] decl 
/
(* *)
let get_event_args table  = 
    match table with
    | DTable {name; loc; keys ;  value ; merge} ->  
      begin match loc with 
      | Some id -> (TINT, id) :: (option_wrapper keys) @ (option_wrapper merge)  
      | None -> [] end                                       
    | _ -> failwith "Only tables allowed"

let get_args preds = List.flatten(List.map get_event_args) *)
  
(* let process_prog (decl : decls) : decls = 
  let base_facts = get_base_facts decl in 
  let filter d tables = match d.d with 
                 | DRule  { DTable {name; loc; keys; value; merge} ; preds; exps} ->  
                 ()
                 | DBaseTable 
                 | _ -> [d.d] *)
(*
let rec generate_context decl ctxt = 
    match decl with 
    | [] -> ctxt 
    |hd :: tl ->  begin match hd.d with 
                  |DTable{name; _} -> 
                   | _ ->  generate_context tl ctxt end *)
  
let generate_table d = match d.d with 
                         | DTable{name; loc; keys; value; merge} ->  let param = 
                         begin match loc with Some v -> [(v, TInt)] | None -> [] end in 
                         let param = param @ keys @ value in 
                         [DGlobal((name), {raw_ty=TName((Cid.create ["Hashtable"; "t"]), [IConst 32], true); teffect=FZero; tspan=d.dspan; tprint_as= TVoid None}, {e=EHash(IConst 2, []); ety=None; espan=d.dspan})
                         ; DEvent((("event_" ^ (fst name)), (snd name)), EEntry(true), [], param )]
                         | _ -> [d.d]

let rec rule_ctxt decl ctxt = 
    match decl with 
    | [] -> ctxt 
    | hd :: tl -> begin match hd.d with 
                              | DRule {lhs=Table{name; loc; args}; _ } -> 
                                    begin match List.assoc_opt name ctxt with 
                                    | Some v ->  let ctxt = (name, ((gensym ("rule_" ^ (fst name))) :: v)) :: ctxt in rule_ctxt tl ctxt
                                    | None -> let ctxt = (name, [(gensym ("rule_" ^ (fst name)))]) :: ctxt in rule_ctxt tl ctxt end
                              | _ -> rule_ctxt tl ctxt end

(* Build Dependency Graph *)

let add_to_list assoc ((Table{name;_} : table), rule)= 
       match List.assoc_opt name assoc with 
                                    | Some v ->   (name, (rule :: v)) :: assoc
                                    | None ->  (name, [rule]) :: assoc

let add_to_graph graph d = match d.d with 
                              | DRule {lhs=Table{name; loc; args}; preds; exps} -> 
                              let t = List.map (fun x -> (x, d.d)) preds in 
                               List.fold add_to_list graph t 
                              | _ -> graph

let create_graph decls = List.fold add_to_graph [] decls


let create_rule_event decls = failwith "unimplemented"

(* Compile Body Event *)
let compile_handler_boody event rule = failwith "unimplemented"
let create_handlers event_list = failwith "unimplemented"


let process_prog (decl : decls) : decls = 
                  let filter d  = match d.d with 
                                 | DRule _ ->  false
                                 | DTable _ -> false 
                                 | _ -> true
in  List.filter (filter) decl ;;