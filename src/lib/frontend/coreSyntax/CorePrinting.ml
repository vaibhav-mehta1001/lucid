open Batteries
open CoreSyntax

let cfg = Cmdline.cfg
let concat_map sep f lst = lst |> List.map f |> String.concat sep
let list_to_string f lst = Printf.sprintf "[%s]" (concat_map "; " f lst)
let comma_sep f xs = concat_map "," f xs

let integer_to_string n =
  if cfg.verbose_types then Integer.to_string n else Integer.value_string n
;;

let location_to_string l = integer_to_string l
let id_to_string id = if cfg.verbose_types then Id.to_string id else Id.name id

let cid_to_string cid =
  if cfg.verbose_types
  then Cid.to_string cid
  else String.concat "." @@ Cid.names cid
;;

let rec size_to_string = string_of_int
let wrap l r str = if String.equal str "" then "" else l ^ str ^ r
let sizes_to_string sizes = comma_sep size_to_string sizes |> wrap "<<" ">>"

let rec raw_ty_to_string t =
  match t with
  | TBool -> "bool"
  | TInt i -> "int<<" ^ size_to_string i ^ ">>"
  | TName (cid, sizes, b) ->
    cid_to_string cid
    ^ sizes_to_string sizes
    ^ if cfg.verbose_types then "{" ^ string_of_bool b ^ "}" else ""
  | TEvent b -> if b then "mevent" else "event"
  | TFun func -> func_to_string func
  | TMemop (size1, size2) ->
    Printf.sprintf
      "memop[int<<%s>>, %s]"
      (size_to_string size1)
      (size_to_string size2)
  | TVoid -> "void"
  | TGroup -> "group"

and func_to_string func =
  let arg_tys = concat_map ", " ty_to_string func.arg_tys in
  let ret_ty = ty_to_string func.ret_ty in
  Printf.sprintf "(%s) -> %s" arg_tys ret_ty

and ty_to_string t = raw_ty_to_string t.raw_ty

let pat_to_string p =
  match p with
  | PWild -> "_"
  | PNum n -> Z.to_string n
  | PBit bs ->
    "0b"
    ^ (bs
      |> List.map (function
             | 0 -> '0'
             | 1 -> '1'
             | _ -> '*')
      |> String.of_list)
;;

let op_to_string op =
  match op with
  (* Unary operators *)
  | Not -> "!"
  | Neg -> "-"
  | BitNot -> "~"
  | Cast size -> "(int<<" ^ size_to_string size ^ ">>)"
  (* Binary operators *)
  | And -> "&&"
  | Or -> "||"
  | Eq -> "=="
  | Neq -> "!="
  | Less -> "<"
  | More -> ">"
  | Leq -> "<="
  | Geq -> ">="
  | Plus -> "+"
  | Sub -> "-"
  | SatPlus -> "|+|"
  | SatSub -> "|-|"
  | Conc -> "^"
  | BitAnd -> "&"
  | BitOr -> "|"
  | BitXor -> "^^"
  | LShift -> "<<"
  | RShift -> ">>"
  | Slice (n, m) -> Printf.sprintf "[%d : %d]" n m
;;

let rec v_to_string v =
  match v with
  | VBool true -> "true"
  | VBool false -> "false"
  | VInt i -> integer_to_string i
  | VEvent event -> event_to_string event
  | VGlobal i -> "global_" ^ string_of_int i
  | VGroup vs -> Printf.sprintf "{%s}" (comma_sep location_to_string vs)

and value_to_string v = v_to_string v.v

and event_to_string { eid; data; edelay; elocations } =
  let locstr =
    match elocations with
    | [] -> "self"
    | _ -> list_to_string location_to_string elocations
  in
  let locstr = if cfg.verbose_types then "@" ^ locstr else "" in
  let delaystr =
    if edelay <> 0 && cfg.verbose_types
    then "@" ^ string_of_int edelay ^ "ns"
    else ""
  in
  Printf.sprintf
    "%s(%s)%s%s"
    (cid_to_string eid)
    (comma_sep value_to_string data)
    delaystr
    locstr
;;

let rec e_to_string e =
  match e with
  | EVal v -> v_to_string v.v
  | EVar cid -> cid_to_string cid
  | EOp (op, [e]) -> op_to_string op ^ exp_to_string e
  | EOp (op, [e1; e2]) -> exp_to_string e1 ^ op_to_string op ^ exp_to_string e2
  | EOp (op, es) ->
    error
      ("wrong number of arguments ("
      ^ string_of_int (List.length es)
      ^ ") to "
      ^ op_to_string op)
  | ECall (cid, es) ->
    Printf.sprintf "%s(%s)" (cid_to_string cid) (es_to_string es)
  | EHash (size, es) ->
    Printf.sprintf "hash<<%s>>(%s)" (size_to_string size) (es_to_string es)

and exp_to_string e = e_to_string e.e
and es_to_string es = comma_sep exp_to_string es

and params_to_string ps =
  comma_sep (fun (i, t) -> ty_to_string t ^ " " ^ id_to_string i) ps

and branch_to_string (ps, s) =
  Printf.sprintf
    "| %s -> {\n%s\n}"
    (comma_sep pat_to_string ps)
    (stmt_to_string s)

and stmt_to_string s =
  match s.s with
  | SAssign (i, e) -> id_to_string i ^ " = " ^ exp_to_string e ^ ";"
  | SNoop -> ""
  | SGen (b, e) ->
    Printf.sprintf "%sgenerate %s;" (if b then "m" else "") (exp_to_string e)
  | SLocal (i, t, e) ->
    Printf.sprintf
      "%s %s = %s;"
      (raw_ty_to_string t.raw_ty)
      (id_to_string i)
      (exp_to_string e)
  | SPrintf (s, es) ->
    Printf.sprintf "printf \"%s\" %s;" s (comma_sep exp_to_string es)
  | SUnit e -> exp_to_string e ^ ";"
  | SIf (e, s1, s2) ->
    let s2_str =
      match s2.s with
      | SNoop -> ""
      | _ -> "else {\n" ^ stmt_to_string s2 ^ "\n}"
    in
    Printf.sprintf
      "if (%s) {\n%s\n} %s"
      (exp_to_string e)
      (stmt_to_string s1)
      s2_str
  | SSeq (s1, s2) ->
    let str1, str2 = stmt_to_string s1, stmt_to_string s2 in
    if str1 = "" then str2 else if str2 = "" then str1 else str1 ^ "\n" ^ str2
  | SMatch (es, branches) ->
    let estr =
      let s = comma_sep exp_to_string es in
      if List.length es = 1 then s else "(" ^ s ^ ")"
    in
    "match " ^ estr ^ " with \n" ^ concat_map "\n" branch_to_string branches
  | SRet eopt ->
    let estr =
      match eopt with
      | Some e -> " " ^ exp_to_string e
      | None -> ""
    in
    Printf.sprintf "return%s;" estr
;;

let statement_to_string = stmt_to_string

let event_sort_to_string sort =
  match sort with
  | EEntry true -> "entry control event"
  | EEntry false -> "entry event"
  | EExit -> "exit event"
  | EBackground -> "event"
;;

let d_to_string d =
  match d with
  | DGlobal (id, ty, exp) ->
    Printf.sprintf
      "global %s %s = %s;\n"
      (ty_to_string ty)
      (id_to_string id)
      (exp_to_string exp)
  | DHandler (id, (params, s)) ->
    Printf.sprintf
      "handle %s(%s) {\n%s\n}"
      (id_to_string id)
      (params_to_string params)
      (stmt_to_string s)
  | DEvent (id, sort, params) ->
    Printf.sprintf
      "%s %s(%s);"
      (event_sort_to_string sort)
      (id_to_string id)
      (params_to_string params)
  | DMemop (id, (params, s)) ->
    Printf.sprintf
      "memop %s(%s)\n {%s}"
      (id_to_string id)
      (params_to_string params)
      (stmt_to_string s)
  | DExtern (id, ty) ->
    Printf.sprintf "extern %s %s;" (id_to_string id) (ty_to_string ty)
  | DGroup (id, es) ->
    Printf.sprintf
      "group %s = {%s};"
      (id_to_string id)
      (comma_sep exp_to_string es)
;;

let decl_to_string d = d_to_string d.d
let decls_to_string ds = concat_map "\n\n" decl_to_string ds
