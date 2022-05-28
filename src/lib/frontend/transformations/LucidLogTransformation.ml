open Syntax
open SyntaxUtils
open Batteries
open Collections
open Printing

(* let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

let option_wrapper opt = 
  match opt with |Some v -> v | None -> []

let get_base_facts decl = 
  let f  l d= match d.d with 
            | DBaseTable(name; _) -> name :: l
in List.fold_left f [] decl 

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
let process_prog (decl : decls) : decls = 
                  let filter d tables = match d.d with 
                                 | DRule _ ->  false
                                 | DTable _ -> false 
                                 | _ -> true
in List.flatten (List.map (filter) decl) ;;