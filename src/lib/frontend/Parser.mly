%{
  open Syntax
  open Batteries
  open SyntaxUtils
  open Collections

  let first (x, _, _, _) = x
  let second (_, x, _, _) = x
  let third (_, _, x, _) = x
  let fourth (_, _, _, x) = x

  let label_sets : StringSet.t list ref = ref []

  let lookup_label sp l =
    match List.find_opt (StringSet.mem l) !label_sets with
    | None -> Console.error_position sp @@ "Unknown label " ^ l
    | Some s -> s

  let fill_erecord base defs sp =
    let label_set = lookup_label sp (fst (List.hd defs)) in
    let undefined_set =
      List.fold_left (fun acc (l, _) -> StringSet.remove l acc) label_set defs
    in
    let all_defs =
      StringSet.fold
        (fun s acc -> (s, proj_sp base s sp) :: acc)
        undefined_set
        defs
    in
    record_sp all_defs sp

  let get_global_sizes span sizes =
    List.map
      (function
        (* | IVar (QVar id) -> id *)
        | IUser id -> Cid.to_id id
        | _ -> Console.error_position span
             "Sizes in a global type/constructor definition must be variables (not begin with a ')")
    sizes

  let mk_dgty id sizes params span =
    let sizes = get_global_sizes span sizes in
    let label_set = StringSet.of_list (List.map (Id.name % fst) params) in
    label_sets := label_set :: !label_sets;
    dgty_sp id sizes params span

  let mk_dconstr constr_id ty_id sizes params body span =
    let sizes = get_global_sizes span sizes in
    dconstr_sp constr_id ty_id sizes params body span

  let mk_tmemop span sizes =
    match sizes with
    | [s1; s2] -> TMemop (s1, TInt s2)
    | _ -> Console.error_position span "Wrong number of size arguments to memop"

  (* We can't use Id.fresh for auto because it messes with regular ids *)
  let auto_count = ref (-1)
  let fresh_auto () =
    incr auto_count;
    Id.create ("auto" ^ string_of_int !auto_count)

  let pat_of_id id =
    if String.equal (Id.name id) "_" then PWild
    else failwith "Parse error: identifiers not allowed in patterns"

%}

%token <Span.t * Id.t> ID
%token <Span.t * Id.t> QID
%token <Span.t * Z.t> NUM
%token <Span.t * int list> BITPAT
%token <Span.t * string> STRING
%token <Span.t> TRUE
%token <Span.t> FALSE
%token <Span.t> EQ
%token <Span.t> NEQ
%token <Span.t> AND
%token <Span.t> OR
%token <Span.t> CONCAT
%token <Span.t> NOT
%token <Span.t> LLEFT
%token <Span.t> RRIGHT
%token <Span.t> LESS
%token <Span.t> MORE
%token <Span.t> PLUS
%token <Span.t> SUB
%token <Span.t> SATSUB
%token <Span.t> ASSIGN
%token <Span.t> IF
%token <Span.t> ELSE
%token <Span.t> SEMI
%token <Span.t> HANDLE
%token <Span.t> FUN
%token <Span.t> MEMOP
%token <Span.t> RETURN
%token <Span.t> PRINTF
%token <Span.t> SIZE
%token <Span.t> LPAREN
%token <Span.t> RPAREN
%token <Span.t> LBRACE
%token <Span.t> RBRACE
%token <Span.t> LBRACKET
%token <Span.t> RBRACKET
%token <Span.t> COMMA
%token <Span.t> DOT
%token <Span.t> TBOOL
%token <Span.t> EVENT
%token <Span.t> MEVENT
%token <Span.t> GENERATE
%token <Span.t> MGENERATE
%token <Span.t> TINT
%token <Span.t> GLOBAL
%token <Span.t> CONST
%token <Span.t> VOID
%token <Span.t> HASH
%token <Span.t> AUTO
%token <Span.t> GROUP
%token <Span.t> CONTROL
%token <Span.t> ENTRY
%token <Span.t> EXIT
%token <Span.t> MATCH
%token <Span.t> WITH
%token <Span.t> PIPE
%token <Span.t> ARROW
%token <Span.t> EXTERN
%token <Span.t> TYPE
%token <Span.t> CONSTR
%token <Span.t> PROJ
%token <Span.t> MODULE
%token <Span.t> BITAND
%token <Span.t> LEQ
%token <Span.t> GEQ
%token <Span.t> COLON
%token <Span.t> LSHIFT
%token <Span.t> RSHIFT
%token <Span.t> END

%token EOF

%start prog
%type  <Syntax.decls> prog

%right ID EVENT
%left AND OR         /* lowest precedence */
%nonassoc LESS EQ MORE NEQ LEQ GEQ
%left PLUS SUB SATSUB
%left CONCAT
%left BITAND PIPE LSHIFT RSHIFT
%nonassoc PROJ
%right NOT RPAREN
%right LBRACKET /* highest precedence */


/* FIXME: the RPAREN thing is a hack to make casting work, and I'm not even sure it's correct
   Same with LBRACKET. */

%%

ty:
    | TINT single_poly                  { ty_sp (TInt (snd $2)) (Span.extend $1 (fst $2)) }
    | TINT                              { ty_sp (TInt (IConst 32)) $1 }
    | TBOOL				                      { ty_sp TBool $1 }
    | QID                               { ty_sp (TQVar (QVar (snd $1))) (fst $1) }
    | AUTO                              { ty_sp (TQVar (QVar (fresh_auto ()))) $1 }
    | cid    				                    { ty_sp (TGlobal ((snd $1, []), FVar (QVar (Id.fresh "eff")))) (fst $1) }
    | cid poly				                  { ty_sp (TGlobal ((snd $1, snd $2), FVar (QVar (Id.fresh "eff")))) (fst $1) }
    | EVENT                             { ty_sp (TEvent false) $1}
    | MEVENT                            { ty_sp (TEvent true) $1}
    | VOID                              { ty_sp (TVoid) $1 }
    | GROUP                             { ty_sp (TGroup) $1 }
    | MEMOP poly                        { ty_sp (mk_tmemop (fst $2) (snd $2)) (Span.extend $1 (fst $2))}

cid:
    | ID				                        { (fst $1, Cid.id (snd $1)) }
    | ID DOT cid                        { (Span.extend (fst $1) (fst $3),
                                            Compound (snd $1, snd $3) )  }
size:
    | NUM                               { fst $1, IConst (Z.to_int (snd $1)) }
    | ID                                { fst $1, IUser (Id (snd $1)) }
    | QID                               { fst $1, IVar (QVar (snd $1)) }
    | AUTO                              { $1, IVar (QVar (fresh_auto ())) }
    | size PLUS size                    { Span.extend (fst $1) (fst $3), add_sizes (snd $1) (snd $3)}

polys:
    | size                              { fst $1, [snd $1] }
    | size COMMA polys                  { Span.extend (fst $1) (fst $3), (snd $1)::(snd $3) }

poly:
    | LLEFT polys RRIGHT                { Span.extend $1 $3, snd $2 }

single_poly:
    | LLEFT size RRIGHT                 { Span.extend $1 $3, snd $2 }

paren_args:
    | LPAREN RPAREN                     { Span.extend $1 $2, [] }
    | LPAREN args RPAREN                { Span.extend $1 $3, $2 }

binop:
    | exp PLUS exp                        { op_sp Plus [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp SUB exp                         { op_sp Sub [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp SATSUB exp                      { op_sp SatSub [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp LESS exp                        { op_sp Less [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp MORE exp                        { op_sp More [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp LEQ exp                         { op_sp Leq [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp GEQ exp                         { op_sp Geq [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp AND exp                         { op_sp And [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp OR exp                          { op_sp Or [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp EQ exp                          { op_sp Eq [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp NEQ exp                         { op_sp Neq [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp BITAND exp                      { op_sp BitAnd [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp PIPE exp                        { op_sp BitOr [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp CONCAT exp                      { op_sp Conc [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp LSHIFT exp                      { op_sp LShift [$1; $3] (Span.extend $1.espan $3.espan) }
    | exp RSHIFT exp                      { op_sp RShift [$1; $3] (Span.extend $1.espan $3.espan) }

exp:
    | cid			                            { var_sp (snd $1) (fst $1) }
    | NUM                                 { eint_sp (snd $1) None (fst $1) }
    | NUM single_poly                     { eint_sp (snd $1) (Some (snd $2)) (Span.extend (fst $1) (fst $2)) }
    | TRUE                                { value_to_exp (vbool_sp true $1) }
    | FALSE                               { value_to_exp (vbool_sp false $1) }
    | cid paren_args                      { call_sp (snd $1) (snd $2) (Span.extend (fst $1) (fst $2)) }
    | binop                               { $1 }
    | NOT exp                             { op_sp Not [$2] (Span.extend $1 $2.espan) }
    | HASH single_poly LPAREN args RPAREN { hash_sp (snd $2) $4 (Span.extend $1 $5) }
    | LPAREN TINT single_poly RPAREN exp  { op_sp (Cast(snd $3))[$5] (Span.extend $1 $5.espan) }
    | exp PROJ ID                         { proj_sp $1 (Id.name (snd $3)) (Span.extend $1.espan (fst $3)) }
    | LPAREN exp RPAREN		             	  { $2 }
    | exp LBRACKET NUM COLON NUM RBRACKET { op_sp (Slice (Z.to_int (snd $3), Z.to_int (snd $5))) [$1]
                                                      (Span.extend ($1).espan (fst $5)) }
    | LBRACE record_entries RBRACE        { record_sp $2 (Span.extend $1 $3) }
    | LBRACE exp WITH record_entries RBRACE { fill_erecord $2 $4 (Span.extend $1 $5) }

record_entry:
    | ID ASSIGN exp                     { Id.name (snd $1), $3 }

record_entries:
    | record_entry                      { [$1] }
    | record_entry SEMI                 { [$1] }
    | record_entry SEMI record_entries  { $1::$3 }

args:
    | exp                               { [$1] }
    | exp COMMA args                    { $1::$3 }

paramsdef:
    | LPAREN RPAREN                     { [] }
    | LPAREN params RPAREN              { $2 }

event_sort:
    | EVENT                             { ($1, EBackground) }
    | ENTRY EVENT                       { ($1, EEntry false) }
    | ENTRY CONTROL EVENT               { ($1, EEntry true) }
    | EXIT EVENT                        { ($1, EExit) }

speclist:
    | cid LESS cid                     { (snd $1, SpecLess) :: [snd $3, SpecLess] }
    | cid LEQ cid                      { (snd $1, SpecLeq) :: [snd $3, SpecLeq] }
    | cid LESS speclist                { (snd $1, SpecLess) :: $3 }
    | cid LEQ speclist                 { (snd $1, SpecLeq) :: $3 }

constr:
    | speclist                          { CSpec $1 }
    | END cid                           { CEnd (snd $2) }

constrs:
    | constr                            { [$1] }
    | constr SEMI constrs               { $1 :: $3 }

constr_list:
    | LBRACKET RBRACKET                 { [] }
    | LBRACKET constrs RBRACKET         { $2 }

interface_spec:
    | FUN ty ID paramsdef SEMI                       { infun_sp (snd $3) $2 [] $4 (Span.extend $1 $5)}
    | FUN ty ID paramsdef constr_list SEMI           { infun_sp (snd $3) $2 $5 $4 (Span.extend $1 $6) }
    | GLOBAL TYPE ID poly ASSIGN LBRACE record_def RBRACE { ingty_sp (snd $3) (get_global_sizes $1 (snd $4)) $7 (Span.extend $1 $8) }
    | GLOBAL TYPE ID ASSIGN LBRACE record_def RBRACE { ingty_sp (snd $3) [] $6 (Span.extend $1 $7) }
    | GLOBAL TYPE ID poly SEMI                       { ingty_sp (snd $3) (get_global_sizes $1 (snd $4)) [] (Span.extend $1 $5) }
    | GLOBAL TYPE ID SEMI                            { ingty_sp (snd $3) [] [] (Span.extend $1 $4) }
    | CONSTR cid poly ID paramsdef SEMI              { inconstr_sp (snd $4) (snd $2) (get_global_sizes $1 (snd $3)) $5 (Span.extend $1 $6) }
    | CONSTR cid ID paramsdef SEMI                   { inconstr_sp (snd $3) (snd $2) [] $4 (Span.extend $1 $5) }
    | ty ID SEMI                                     { invar_sp (snd $2) $1 (Span.extend ($1.tspan) $3) }
    | EVENT ID paramsdef SEMI                        { inevent_sp (snd $2) [] $3 (Span.extend $1 $4) }
    | EVENT ID paramsdef constr_list SEMI            { inevent_sp (snd $2) $4 $3 (Span.extend $1 $5) }
    | SIZE ID SEMI                                   { insize_sp (snd $2) (Span.extend $1 $3) }
    | MODULE ID COLON LBRACE interface RBRACE        { inmodule_sp (snd $2) $5 (Span.extend $1 $6) }

interface:
    | interface_spec                    { [$1] }
    | interface_spec interface          { $1::$2 }

event_decl:
    | event_sort ID paramsdef             { ($1, snd $2, $3, []) }
    | event_sort ID paramsdef constr_list { ($1, snd $2, $3, $4) }

decl:
    | CONST ty ID ASSIGN exp SEMI           { [dconst_sp (snd $3) $2 $5 (Span.extend $1 $6)] }
    | EXTERN ty ID SEMI                     { [dextern_sp (snd $3) $2 (Span.extend $1 $4)] }
    | event_decl SEMI                       { [event_sp (second $1) (snd (first $1)) (fourth $1) (third $1) (Span.extend (fst (first $1)) $2)] }
    | event_decl LBRACE statement RBRACE    { [event_sp (second $1) (snd (first $1)) (fourth $1) (third $1) (Span.extend (fst (first $1)) $4);
                                               handler_sp (second $1) (third $1) $3 (Span.extend (fst (first $1)) $4)] }
    | HANDLE ID paramsdef LBRACE statement RBRACE
      	     	       	      	     	        { [handler_sp (snd $2) $3 $5 (Span.extend $1 $6)] }
    | FUN ty ID paramsdef LBRACE statement RBRACE
                                            { [fun_sp (snd $3) $2 [] $4 $6 (Span.extend $1 $7)] }
    | FUN ty ID paramsdef constr_list LBRACE statement RBRACE
                                            { [fun_sp (snd $3) $2 $5 $4 $7 (Span.extend $1 $8)] }
    | MEMOP ID paramsdef LBRACE statement RBRACE
                                            { [memop_sp (snd $2) $3 $5 (Span.extend $1 $6)] }
    | SIZE ID ASSIGN size SEMI              { [dsize_sp (snd $2) (snd $4) (Span.extend $1 (fst $4))] }
    | GROUP ID ASSIGN LBRACE args RBRACE SEMI { [group_sp (snd $2) $5 (Span.extend $1 $6)] }
    | MODULE ID LBRACE decls RBRACE         { [module_sp (snd $2) [] $4 (Span.extend $1 $5)] }
    | MODULE ID COLON LBRACE interface RBRACE LBRACE decls RBRACE
                                            { [module_sp (snd $2) $5 $8 (Span.extend $1 $9)] }
    | GLOBAL TYPE ID poly ASSIGN LBRACE record_def RBRACE { [mk_dgty (snd $3) (snd $4) $7 (Span.extend $1 $8)] }
    | CONSTR cid poly ID paramsdef LBRACE decls RBRACE { [mk_dconstr (snd $4) (snd $2) (snd $3) $5 $7 (Span.extend $1 $8)] }
    | GLOBAL cid poly ID ASSIGN cid paren_args SEMI
                                            { [dglobal_sp (snd $4) (snd $2, snd $3) (snd $6) (snd $7) (Span.extend $1 $8)] }
    | GLOBAL TYPE ID ASSIGN LBRACE record_def RBRACE { [mk_dgty (snd $3) [] $6 (Span.extend $1 $7)] }
    | CONSTR cid ID paramsdef LBRACE decls RBRACE { [mk_dconstr (snd $3) (snd $2) [] $4 $6 (Span.extend $1 $7)] }
    | GLOBAL cid ID ASSIGN cid paren_args SEMI
                                            { [dglobal_sp (snd $3) (snd $2, []) (snd $5) (snd $6) (Span.extend $1 $7)] }

decls:
    | decl                             { $1 }
    | decl decls                       { $1 @ $2 }

param:
    | ty ID				                     { (snd $2, $1) }

params:
    | param				                      { [ $1 ] }
    | param COMMA params                { $1 :: $3 }

record_def:
    | param	SEMI			                 { [ $1 ] }
    | param SEMI record_def            { $1 :: $3 }

pattern:
    | ID                                { pat_of_id (snd $1) }
    | NUM                               { PNum (snd $1) }
    | BITPAT                            { PBit (snd $1) }

patterns:
  | pattern                             { [$1] }
  | pattern COMMA patterns              { $1 :: $3 }

statement:
    | statement0			                  { $1 }
    | statement0 statement              { sseq_sp $1 $2 (Span.extend $1.sspan $2.sspan) }

statement0:
    | matched				                    { $1 }
    | unmatched				                  { $1 }
    | statement1                        { $1 }

matched:
    | IF LPAREN exp RPAREN LBRACE statement RBRACE ELSE LBRACE statement RBRACE
                                        { sifte_sp $3 $6 $10 (Span.extend $1 $11) }
unmatched:
    | IF LPAREN exp RPAREN LBRACE statement RBRACE ELSE unmatched
                                        { sifte_sp $3 $6 $9 (Span.extend $1 $9.sspan)}
    | IF LPAREN exp RPAREN LBRACE statement RBRACE
                                        { sifte_sp $3 $6 snoop (Span.extend $1 $7)}

branch:
    | PIPE patterns ARROW LBRACE statement RBRACE  { Span.extend $1 $6, ($2, $5) }

branches:
    | branch                                 { fst $1, [snd $1] }
    | branch branches                        { Span.extend (fst $1) (fst $2), (snd $1::snd $2) }

(* Only needed to avoid a shift-reduce warning on with match statemnets.
   We'd get the same result either way, though. *)
multiargs:
    | exp COMMA args                         { $1::$3 }

statement1:
    | ty ID ASSIGN exp SEMI                 { slocal_sp (snd $2) $1 $4 (Span.extend $1.tspan $5) }
    | ID ASSIGN exp SEMI	                  { sassign_sp (snd $1) $3 (Span.extend (fst $1) $4) }
    | RETURN SEMI                           { sret_sp None (Span.extend $1 $2) }
    | RETURN exp SEMI                       { sret_sp (Some $2) (Span.extend $1 $3) }
    | GENERATE exp SEMI                     { gen_sp false $2 (Span.extend $1 $3)}
    | MGENERATE exp SEMI                    { gen_sp true $2 (Span.extend $1 $3)}
    | cid paren_args SEMI                   { scall_sp (snd $1) (snd $2) (Span.extend (fst $1) $3) }
    | MATCH args WITH branches              { match_sp $2 (snd $4) (Span.extend $1 (fst $4)) }
    | MATCH LPAREN multiargs RPAREN WITH branches  { match_sp $3 (snd $6) (Span.extend $1 (fst $6)) }
    | PRINTF LPAREN STRING RPAREN SEMI             { sprintf_sp (snd $3) [] (Span.extend $1 $5) }
    | PRINTF LPAREN STRING COMMA args RPAREN SEMI  { sprintf_sp (snd $3) $5 (Span.extend $1 $7) }

prog:
    | decls EOF                             { $1 }
;
