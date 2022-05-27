open Syntax
open SyntaxUtils
open Batteries
open Collections
open Printing

let process_prog (decl : decls) : decls = 
  let filter d = match d.d with 
                 | DRule _-> false 
                 | _ -> true 
in List.filter (filter) decl ;;