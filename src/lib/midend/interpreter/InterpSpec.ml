open Batteries
open CoreSyntax
open Yojson.Basic
open Preprocess
module Env = InterpState.Env
module IntMap = InterpState.IntMap

(* Maps switch -> port -> (switch * port) *)

type t =
  { num_switches : int
  ; links : InterpState.State.topology
  ; externs : value Env.t list
  ; events : (event * (int * int) list) list
  ; config : InterpState.State.config
  }

let rename env err_str id_str =
  match Collections.CidMap.find_opt (Cid.from_string id_str) env with
  | Some id -> id
  | None -> error @@ Printf.sprintf "Unknown %s %s" err_str id_str
;;

let parse_int err_str (j : json) =
  match j with
  | `Int n -> n
  | _ -> error @@ "Non-integer value for " ^ err_str
;;

let parse_int_entry lst str default =
  match List.assoc_opt str lst with
  | Some j -> parse_int str j
  | None -> default
;;

let rec parse_value err_str ty j =
  match j, ty.raw_ty with
  | `Int n, TInt size -> vint n size
  | `Bool b, TBool -> vbool b
  | `List lst, TGroup ->
    vgroup
      (List.map
         (fun n -> Integer.of_int @@ parse_int "group value definition" n)
         lst)
  | _ ->
    error
    @@ err_str
    ^ " specification had wrong or unexpected argument "
    ^ to_string j
;;

let parse_port str =
  match String.split_on_char ':' str with
  | [id; port] ->
    (try int_of_string id, int_of_string port with
    | _ -> error "Incorrect format for link entry!")
  | _ -> error "Incorrect format for link entry!"
;;

let default_port = 0

let parse_events
    (pp : Preprocess.t)
    (renaming : Renaming.env)
    (num_switches : int)
    (gap : int)
    (events : json list)
  =
  (* Using state because I'm lazy *)
  let last_delay = ref (-gap) in
  let parse_event (event : json) =
    match event with
    | `Assoc lst ->
      (* Find the event name, accounting for the renaming pass, and get its
         sort and argument types *)
      let eid =
        match List.assoc "name" lst with
        | `String id -> rename renaming.var_map "event" id
        | _ -> error "Event specification had wrong type for name field"
      in
      let sort, tys = Env.find eid pp.events in
      if sort = EExit then error "Cannot specify exit event";
      (* Parse the arguments into values, and make sure they have the right types.
         At the moment only integer and boolean arguments are supported *)
      let data =
        match List.assoc "args" lst with
        | `List lst ->
          (try List.map2 (parse_value "Event") tys lst with
          | Invalid_argument _ ->
            error
            @@ Printf.sprintf
                 "Event specification for %s had wrong number of arguments"
                 (Cid.to_string eid))
        | _ -> error "Event specification had non-list type for arguments"
      in
      (* Parse the delay and location fields, if they exist *)
      let edelay =
        match List.assoc_opt "timestamp" lst with
        | Some (`Int n) ->
          last_delay := n;
          n
        | None ->
          last_delay := !last_delay + gap;
          !last_delay
        | _ -> error "Event specification had non-integer delay field"
      in
      let locations =
        match List.assoc_opt "locations" lst with
        | Some (`List lst) ->
          List.map
            (function
              | `String str ->
                let sw, port = parse_port str in
                if sw < 0 || sw >= num_switches
                then
                  error
                  @@ "Cannot specify event at nonexistent switch "
                  ^ string_of_int sw;
                if port < 0 || port >= 255
                then
                  error
                  @@ "Cannot specify event at nonexistent port "
                  ^ string_of_int port;
                sw, port
              | _ -> error "Event specification had non-string location")
            lst
        | None -> [0, default_port]
        | _ -> error "Event specification has non-list locations field"
      in
      { eid; data; edelay }, locations
    | _ -> error "Non-assoc type for event definition"
  in
  List.map parse_event events
;;

let builtins renaming n =
  List.init n (fun i ->
      Env.singleton (rename renaming "self" "self") (vint i 32))
;;

let parse_externs
    (pp : Preprocess.t)
    (renaming : Renaming.env)
    (num_switches : int)
    (externs : (string * json) list)
  =
  List.fold_left
    (fun acc (id, values) ->
      let id = rename renaming.var_map "extern" id in
      let ty = Env.find id pp.externs in
      let vs =
        match values with
        | `List lst -> List.map (parse_value "Extern" ty) lst
        | _ -> error "Non-list type for extern value specification"
      in
      if List.length vs <> num_switches
      then
        error
        @@ "Number of values for extern "
        ^ Cid.to_string id
        ^ " does not match number of switches";
      List.map2 (fun env v -> Env.add id v env) acc vs)
    (builtins renaming.var_map num_switches)
    externs
;;

let parse_links num_switches links =
  let add_link id port dst acc =
    IntMap.modify
      id
      (fun map ->
        match IntMap.find_opt port map with
        | None -> IntMap.add port dst map
        | Some dst' when dst = dst' -> map
        | _ ->
          error
          @@ Printf.sprintf
               "Switch:port pair %d:%d assigned to two different destinations!"
               id
               port)
      acc
  in
  let add_links acc (src, dst) =
    let src_id, src_port = parse_port src in
    let dst_id, dst_port =
      match dst with
      | `String dst -> parse_port dst
      | _ -> error "Non-string format for link entry!"
    in
    acc
    |> add_link src_id src_port (dst_id, dst_port)
    |> add_link dst_id dst_port (src_id, src_port)
  in
  List.fold_left add_links (InterpState.State.empty_topology num_switches) links
;;

(* Make a full mesh with arbitrary port numbers.
   Specifically, we map 1:2 to 2:1, and 3:4 to 4:3, etc. *)
let make_full_mesh num_switches =
  let switch_ids = List.init num_switches (fun n -> n) in
  List.fold_left
    (fun acc id ->
      let port_map =
        List.fold_left
          (fun acc port ->
            if id = port then acc else IntMap.add port (port, id) acc)
          IntMap.empty
          switch_ids
      in
      IntMap.add id port_map acc)
    IntMap.empty
    switch_ids
;;

let parse (pp : Preprocess.t) (renaming : Renaming.env) (filename : string) : t =
  let json = from_file filename in
  match json with
  | `Assoc lst ->
    let parse_int_entry = parse_int_entry lst in
    let num_switches = parse_int_entry "switches" 1 in
    let default_input_gap = parse_int_entry "default input gap" 0 in
    let generate_delay = parse_int_entry "generate delay" 600 in
    let propagate_delay = parse_int_entry "propagate delay" 0 in
    let random_delay_range = parse_int_entry "random delay range" 1 in
    let random_propagate_range = parse_int_entry "random propagate range" 1 in
    let random_seed =
      parse_int_entry "random seed" (int_of_float @@ Unix.time ())
    in
    let links =
      if num_switches = 1
      then IntMap.empty
      else (
        match List.assoc_opt "links" lst with
        | Some (`Assoc links) -> parse_links num_switches links
        | Some (`String "full mesh") -> make_full_mesh num_switches
        | _ -> error "Unexpected format or missing edge declarations")
    in
    let max_time =
      match List.assoc_opt "max time" lst with
      | Some (`Int n) -> n
      | _ -> error "No value or non-int value specified for max time"
    in
    let externs =
      let lst =
        match List.assoc_opt "externs" lst with
        | Some (`Assoc lst) -> lst
        | None -> []
        | Some _ -> error "Non-assoc type for extern definitions"
      in
      parse_externs pp renaming num_switches lst
    in
    let events =
      match List.assoc_opt "events" lst with
      | Some (`List lst) ->
        parse_events pp renaming num_switches default_input_gap lst
      | _ -> error "No or non-list value for event definitions"
    in
    let config : InterpState.State.config =
      { max_time
      ; generate_delay
      ; propagate_delay
      ; random_delay_range
      ; random_propagate_range
      ; random_seed
      }
    in
    { num_switches; links; externs; events; config }
  | _ -> error "Unexpected interpreter specification format"
;;
