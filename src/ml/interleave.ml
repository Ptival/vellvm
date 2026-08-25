(* Driver scaffolding for interleaved execution of two LLVM programs. *)
open VellvmLib

(* Load one side of the interleaving, returning its itree and, when the entry was
   chosen with [-entry], a description of the call it starts from. With no
   [-entry] this is the usual whole-program run from @main; either way
   [denote_vellvm] initializes the globals before reaching the entry. *)
let build_itree args link_files (path, entry) =
  let ast = IO.parse_file path in
  let linked_ast = TopLevel.link_all link_files ast in
  match entry with
  | None ->
      (TopLevel.interpreter (List.map Camlcoq.coqstring_of_camlstring args) linked_ast, None)
  | Some spec ->
      let resolved = Entry.resolve ~context:(Filename.basename path) linked_ast spec in
      (Entry.interpreter resolved linked_ast, Some (Entry.describe resolved))

type focus = Left | Right

type command =
  | FocusLeft
  | FocusRight
  | Step
  | PrintLocals
  | PrintGlobals
  | PrintTree

type 'tree session =
  { mutable tree : 'tree option;
    mutable stack : Stack.stack_frame list;
    mutable globals : Global.global_env;
    mutable location : string;
  }

let read_command focus last_command =
  Printf.printf "%s" (match focus with Left -> "([l] r )> " | Right -> "( l [r])> ");
  match read_line () with
  | "" ->
    if last_command == None then Printf.printf "No previous command to repeat.\n";
    last_command
  | "left" | "l" -> Some FocusLeft
  | "right" | "r" -> Some FocusRight
  | "step" | "s" -> Some Step
  | "pl" -> Some PrintLocals
  | "pg" -> Some PrintGlobals
  | "pt" -> Some PrintTree
  | _ ->
      Printf.printf "Invalid command. Expected left (l), right (r), step (s), pl, pg, or pt.\n";
      None

let report_result side = function
  | Ok value ->
      Printf.printf "%s program terminated with: %s\n"
        side (Interpreter.string_of_dvalue value)
  | Error error ->
      Printf.printf "%s program stopped with: %s\n"
        side (Result.string_of_exit_condition error)

let show_location location =
  if location = "" then "<unknown>"
  else
    match Debugger.location_parse location with
    | None -> location
    | Some file_location ->
        let file_location = { file_location with file = Filename.basename file_location.file } in
        "[" ^ Debugger.show_file_location file_location ^ "]"

let show_type typ =
  Camlcoq.camlstring_of_coqstring (ReprAST.repr_dtyp typ)

let show_output bytes =
  let output = Interpreter.string_of_bytes bytes in
  Printf.sprintf "%d byte(s), %S" (Bytes.length output) (Bytes.to_string output)

let describe_visible_event location = function
  | Sum.Coq_inl1 (LLVMEvents.ExternalCall (typ, callee, args)) ->
      Printf.sprintf "VisF (external call: %s %s with %d argument(s), at %s)"
        (show_type typ) (Interpreter.string_of_dvalue callee)
        (List.length args) (show_location location)
  | Sum.Coq_inl1 (LLVMEvents.IO_stdout bytes) ->
      Printf.sprintf "VisF (stdout: %s, at %s)"
        (show_output bytes) (show_location location)
  | Sum.Coq_inl1 (LLVMEvents.IO_stderr bytes) ->
      Printf.sprintf "VisF (stderr: %s, at %s)"
        (show_output bytes) (show_location location)
  | Sum.Coq_inr1 (Sum.Coq_inl1 _) ->
      Printf.sprintf "VisF (out of memory, at %s)" (show_location location)
  | Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 exception_value)) ->
      Printf.sprintf "VisF (LLVM exception: %s, at %s)"
        (Interpreter.string_of_dvalue exception_value) (show_location location)
  | Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _))) ->
      Printf.sprintf "VisF (undefined behavior, at %s)" (show_location location)
  | Sum.Coq_inr1
      (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _)))) ->
      Printf.sprintf "VisF (debug event, at %s)" (show_location location)
  | Sum.Coq_inr1
      (Sum.Coq_inr1
        (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _)))) ->
      Printf.sprintf "VisF (failure, at %s)" (show_location location)

let describe_next_node session =
  match session.tree with
  | None -> "stopped (no next node)"
  | Some tree ->
      match ITreeDefinition.observe tree with
      | ITreeDefinition.TauF _ ->
          Printf.sprintf "TauF (internal transition, at %s)"
            (show_location session.location)
      | ITreeDefinition.RetF _ -> "RetF (return)"
      | ITreeDefinition.VisF (event, _) ->
          describe_visible_event session.location event

let report_next_node side session =
  let description = describe_next_node session in
  Printf.printf "%s next node: %s.\n" side description

let report_step node session =
  Printf.printf "At %s, %d stack frame(s), %d global(s).\n"
    node (List.length session.stack)
    (List.length (RawIdMaps.RM.elements session.globals))

let publish_globals session =
  (Global.globals_object Interpreter.params).globals_set session.globals

let publish_stack session =
  let observer = Stack.local_stack_object Interpreter.params in
  let current_stack = observer.local_stack_get () in
  List.iter (fun _ -> observer.local_stack_pop ()) current_stack;
  List.iter observer.local_stack_push (List.rev session.stack)

let publish_observers session =
  publish_globals session;
  publish_stack session

let capture_observers session =
  session.stack <-
    (Stack.local_stack_object Interpreter.params).local_stack_get ();
  session.globals <-
    (Global.globals_object Interpreter.params).globals_get ();
  session.location <-
    Camlcoq.camlstring_of_coqstring
      (LLVMEvents.printer_object.printer_get_loc ())

let newly_introduced old_values new_values =
  RawIdMaps.RM.fold
    (fun identifier value introduced ->
      if RawIdMaps.RM.mem identifier old_values then introduced
      else RawIdMaps.RM.add identifier value introduced)
    new_values RawIdMaps.RM.empty

let report_new_globals old_globals new_globals =
  let introduced = newly_introduced old_globals new_globals in
  if not (RawIdMaps.RM.is_empty introduced) then begin
    Printf.printf "New globals:\n";
    Debugger.print_globals introduced
  end

let report_new_locals old_stack new_stack =
  let old_length = List.length old_stack in
  let new_length = List.length new_stack in
  let old_offset = old_length - new_length in
  let printed_heading = ref false in
  List.iteri
    (fun frame_number (frame : Stack.stack_frame) ->
      let old_frame_number = frame_number + old_offset in
      let old_vars =
        if old_frame_number < 0 then RawIdMaps.RM.empty
        else
          match List.nth_opt old_stack old_frame_number with
          | None -> RawIdMaps.RM.empty
          | Some (old_frame : Stack.stack_frame) -> old_frame.stack_vars
      in
      let introduced = newly_introduced old_vars frame.stack_vars in
      if not (RawIdMaps.RM.is_empty introduced) then begin
        if not !printed_heading then begin
          Printf.printf "New locals:\n";
          printed_heading := true
        end;
        let location =
          match frame.stack_loc with
          | None -> "_"
          | Some value ->
              show_location (Camlcoq.camlstring_of_coqstring value)
        in
        Printf.printf "Stack frame #%d (%s):\n" frame_number location;
        Debugger.print_stack_frame_vars { frame with stack_vars = introduced }
      end)
    new_stack

let report_introduced old_globals old_stack session =
  report_new_globals old_globals session.globals;
  report_new_locals old_stack session.stack

let print_itree session =
  let max_lines = 10 in
  let rec print_materialized line tree =
    if line < max_lines then
      match ITreeDefinition.observe tree with
      | ITreeDefinition.RetF _ ->
          Printf.printf "%d: RetF (return)\n" line
      | ITreeDefinition.VisF (event, _) ->
          Printf.printf "%d: %s\n" line
            (describe_visible_event session.location event);
          if line + 1 < max_lines then
            Printf.printf "%d: <continuation requires an event result>\n"
              (line + 1)
      | ITreeDefinition.TauF next ->
          Printf.printf "%d: TauF (internal transition, at %s)\n"
            line (show_location session.location);
          if line + 1 < max_lines then
            if Lazy.is_val next then print_materialized (line + 1) next
            else
              Printf.printf "%d: <lazy continuation not forced>\n" (line + 1)
  in
  match session.tree with
  | None -> Printf.printf "0: <stopped; no ITree>\n"
  | Some tree -> print_materialized 0 tree

(** Interactively advance two independently retained Vellvm ITrees. *)
let rec command_loop left right focus last_command =
  match read_command focus last_command with
  | exception End_of_file -> ()
  | None -> command_loop left right focus last_command
  | Some FocusLeft ->
      (match focus with
       | Left -> Printf.printf "Left program is already focused.\n"
       | Right ->
           Printf.printf "Focus changed to left program.\n";
           publish_observers left;
           report_next_node "Left" left;
           capture_observers left);
      command_loop left right Left (Some FocusLeft)
  | Some FocusRight ->
      (match focus with
       | Left ->
           Printf.printf "Focus changed to right program.\n";
           publish_observers right;
           report_next_node "Right" right;
           capture_observers right
       | Right -> Printf.printf "Right program is already focused.\n");
      command_loop left right Right (Some FocusRight)
  | Some PrintLocals ->
      let stack = match focus with Left -> left.stack | Right -> right.stack in
      Debugger.print_stack_vars stack;
      command_loop left right focus (Some PrintLocals)
  | Some PrintGlobals ->
      let globals =
        match focus with Left -> left.globals | Right -> right.globals
      in
      Debugger.print_globals globals;
      command_loop left right focus (Some PrintGlobals)
  | Some PrintTree ->
      let session = match focus with Left -> left | Right -> right in
      publish_observers session;
      print_itree session;
      capture_observers session;
      command_loop left right focus (Some PrintTree)
  | Some Step ->
      match focus with
      | Left ->
          (match left.tree with
           | None ->
               Printf.printf "Left program has already stopped.\n";
               command_loop left right focus (Some Step)
           | Some tree ->
               let old_globals = left.globals in
               let old_stack = left.stack in
               publish_observers left;
               let node = describe_next_node left in
               match Interpreter.single_step tree with
               | Either.Left next ->
                   left.tree <- Some next;
                   capture_observers left;
                   report_step node left;
                   report_introduced old_globals old_stack left;
                   command_loop left right focus (Some Step)
               | Either.Right result ->
                   left.tree <- None;
                   capture_observers left;
                   report_step node left;
                   report_result "Left" result;
                   report_introduced old_globals old_stack left;
                   command_loop left right focus (Some Step))
      | Right ->
          (match right.tree with
           | None ->
               Printf.printf "Right program has already stopped.\n";
               command_loop left right focus (Some Step)
           | Some tree ->
               let old_globals = right.globals in
               let old_stack = right.stack in
               publish_observers right;
               let node = describe_next_node right in
               match Interpreter.single_step tree with
               | Either.Left next ->
                   right.tree <- Some next;
                   capture_observers right;
                   report_step node right;
                   report_introduced old_globals old_stack right;
                   command_loop left right focus (Some Step)
               | Either.Right result ->
                   right.tree <- None;
                   capture_observers right;
                   report_step node right;
                   report_result "Right" result;
                   report_introduced old_globals old_stack right;
                   command_loop left right focus (Some Step))

let interleave_itrees left right =
  let initial_stack =
    (Stack.local_stack_object Interpreter.params).local_stack_get ()
  in
  let initial_globals =
    (Global.globals_object Interpreter.params).globals_get ()
  in
  let initial_location =
    Camlcoq.camlstring_of_coqstring
      (LLVMEvents.printer_object.printer_get_loc ())
  in
  command_loop
    { tree = Some left;
      stack = initial_stack;
      globals = initial_globals;
      location = initial_location;
    }
    { tree = Some right;
      stack = initial_stack;
      globals = initial_globals;
      location = initial_location;
    }
    Left None

(* Each side is given its own (path, entry) pair: the two programs are resolved
   independently, so they may start from different arguments. *)
let interleave args link_files (left_path, _ as left_side) (right_path, _ as right_side) =
  Out_channel.set_buffered stdout false;
  Out_channel.set_buffered stderr false;
  let left, left_entry = build_itree args link_files left_side in
  let right, right_entry = build_itree args link_files right_side in
  let describe path = function
    | None -> Filename.basename path
    | Some entry -> Printf.sprintf "%s, from %s" (Filename.basename path) entry
  in
  Printf.printf " Left file: %s\n" (describe left_path left_entry);
  Printf.printf "Right file: %s\n" (describe right_path right_entry);
  interleave_itrees left right;
