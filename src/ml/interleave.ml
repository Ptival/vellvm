(* Driver scaffolding for interleaved execution of two LLVM programs. *)
open VellvmLib

(* One side of the interleaving: the program, the entry to start it from, the
   `argv` to give @main when there is no entry, and the .ll files linked into this
   side only. The two sides most often need to differ -- a different entry,
   different buffers, a different hand-written harness -- so everything that
   selects what to run is per side; only the files linked with -l/-L are shared.
   This is what a `.vellvm` manifest describes, and what the -entry-* flags build
   for a side named by a bare .ll file. *)
type side =
  { label : string;
    path : string;
    entry : Entry.spec option;
    argv : string list option;
    links : TopLevel.ll_toplevel_entities list;
    skip_init : bool;  (* this side's own `skip-init:`; -skip-init asks for both *)
  }

(* Load one side of the interleaving, returning its itree, a description of the
   call it starts from when an entry was chosen, and -- when this side is to be
   advanced past its initialization -- how many stack frames deep that call sits,
   which is what [Interpreter.skip_initialization] needs. With no entry this is
   the usual whole-program run from @main, with the side's own `argv` if it has one
   and [-args] otherwise; either way [denote_vellvm] initializes the globals
   before reaching the entry. *)
let build_itree args shared_links side =
  let ast = IO.parse_file side.path in
  let linked_ast = TopLevel.link_all (side.links @ shared_links) ast in
  (* A manifest may ask for the skip on its own program, and [-skip-init] asks for
     it on every program; neither contradicts the other, since this changes only
     where stepping begins and not what the program does. *)
  let skip frames =
    if side.skip_init || !Interpreter.skip_init then Some frames else None
  in
  match side.entry with
  | None ->
      let argv = Option.value side.argv ~default:args in
      ( TopLevel.interpreter (List.map Camlcoq.coqstring_of_camlstring argv) linked_ast
      , None
      , skip 1 )
  | Some spec ->
      (* [resolve] may link a generated harness into the program, so the itree is
         built from the program it hands back rather than from [linked_ast]. *)
      let resolved = Entry.resolve ~context:side.label linked_ast spec in
      ( Entry.interpreter resolved
      , Some (Entry.describe resolved)
      , skip resolved.Entry.frames_to_entry )

type focus = Left | Right

type command =
  | FocusLeft
  | FocusRight
  | Step
  | StepITree
  | StepCall
  | Examine of string * int
  | PrintLocals
  | PrintGlobals
  | PrintTree

type 'tree session =
  { mutable tree : 'tree option;
    source_path : string;
    mutable memory : Memory0.memory;
    mutable stack : Stack.stack_frame list;
    mutable globals : Global.global_env;
    mutable location_state : LLVMAst.file_info option;
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
  | "stepi" | "si" -> Some StepITree
  | "stepc" | "sc" -> Some StepCall
  | "pl" -> Some PrintLocals
  | "pg" -> Some PrintGlobals
  | "pt" -> Some PrintTree
  | input ->
      (match Str.split (Str.regexp "[ \t]+") (String.trim input) with
       | ["x"; local; count] ->
           (match int_of_string_opt count with
            | Some count when count > 0 && count <= 4096 -> Some (Examine (local, count))
            | _ ->
                Printf.printf "The byte count must be between 1 and 4096.\n";
                None)
       | _ ->
           Printf.printf
             "Invalid command. Expected left (l), right (r), step (s), stepi (si), \
              stepc (sc), x <local> <bytes>, pl, pg, or pt.\n";
           None)

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
  publish_stack session;
  (Memory0.memory_object Interpreter.params).memory_set session.memory;
  ignore (LLVMEvents.printer_object.printer_set_loc session.location_state)

let capture_observers session =
  session.memory <-
    (Memory0.memory_object Interpreter.params).memory_get ();
  session.stack <-
    (Stack.local_stack_object Interpreter.params).local_stack_get ();
  session.globals <-
    (Global.globals_object Interpreter.params).globals_get ();
  session.location_state <-
    LLVMEvents.printer_object.printer_get_loc_state ();
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

let normalize_local_name name =
  let name = String.trim name in
  if String.length name > 0 && name.[0] = '%' then String.sub name 1 (String.length name - 1)
  else name

let find_local name stack =
  let name = normalize_local_name name in
  let identifier =
    match int_of_string_opt name with
    | Some number when number >= 0 -> LLVMAst.Anon (Camlcoq.Z.of_sint number)
    | _ -> LLVMAst.Name (Camlcoq.coqstring_of_camlstring name)
  in
  let rec find = function
    | [] -> None
    | (frame : Stack.stack_frame) :: frames ->
        (match RawIdMaps.RM.find identifier frame.stack_vars with
         | Some value -> Some value
         | None -> find frames)
  in
  find stack

let byte_string memory pointer offset =
  let params = Interpreter.params in
  let address =
    BinInt.Z.add (params.coq_P2I.ptr_to_int pointer) (Camlcoq.Z.of_sint offset)
  in
  match Memory0.read_byte_raw_mem params memory address with
  | None -> "--"
  | Some (byte, allocation_id) ->
      if not (params.coq_PROV.access_allowed (params.coq_PTR.ptr_provenance pointer) allocation_id)
      then "!!"
      else
        match MemoryBytes.memory_byte_value params byte with
        | EOU.Coq_raise_ret (MemoryBytes.NoPois value) ->
            Printf.sprintf "%02x" (Camlcoq.Z.to_int value land 0xff)
        | EOU.Coq_raise_ret MemoryBytes.Pois -> "pp"
        | EOU.Coq_raise_error _ | EOU.Coq_raise_oom _ | EOU.Coq_raise_ub _ -> "??"

let examine_memory session local count =
  match find_local local session.stack with
  | None -> Printf.printf "No local named %%%s is in scope.\n" (normalize_local_name local)
  | Some (DynamicValues.DVALUE_Base (DynamicValues.DVALUE_Pointer pointer)) ->
      let base = Interpreter.params.coq_P2I.ptr_to_int pointer in
      for row = 0 to (count - 1) / 16 do
        let offset = row * 16 in
        let width = min 16 (count - offset) in
        let address = BinInt.Z.add base (Camlcoq.Z.of_sint offset) in
        let bytes =
          List.init width (fun index -> byte_string session.memory pointer (offset + index))
        in
        Printf.printf "%s: %s\n" (Camlcoq.Z.to_string address) (String.concat " " bytes)
      done;
      Printf.printf "(-- unallocated, !! invalid provenance, pp poison, ?? symbolic)\n"
  | Some value ->
      Printf.printf "%s is not a pointer (it is %s).\n" local
        (Interpreter.string_of_dvalue value)

let state_changed old_globals old_stack old_location session =
  old_location <> session.location
  || old_globals <> session.globals
  || old_stack <> session.stack

let next_node_is_boundary tree =
  match ITreeDefinition.observe tree with
  | ITreeDefinition.TauF _ -> false
  | ITreeDefinition.RetF _ | ITreeDefinition.VisF _ -> true

let step_limit = 10_000

let source_cache = Hashtbl.create 2

let source_lines path =
  match Hashtbl.find_opt source_cache path with
  | Some lines -> Some lines
  | None ->
      (match
         try
           Some
             (In_channel.with_open_text path (fun channel ->
                In_channel.input_all channel
                |> String.split_on_char '\n'
                |> Array.of_list))
         with Sys_error _ -> None
       with
       | None -> None
       | Some lines ->
           Hashtbl.add source_cache path lines;
           Some lines)

let source_path_for_location source_path filename =
  if Filename.basename source_path = Filename.basename filename then Some source_path
  else if Sys.file_exists filename then Some filename
  else
    let relative_to_source = Filename.concat (Filename.dirname source_path) filename in
    if Sys.file_exists relative_to_source then Some relative_to_source else None

let source_location_lines session =
  match session.location_state with
  | None -> []
  | Some (file_info : LLVMAst.file_info) ->
      let filename = Camlcoq.camlstring_of_coqstring file_info.filename in
      (match source_path_for_location session.source_path filename with
       | None -> []
       | Some path ->
           match source_lines path with
           | None -> []
           | Some lines ->
               let first = Camlcoq.Z.to_int file_info.start_line in
               let last = Camlcoq.Z.to_int file_info.end_line in
               if first >= 1 && first <= last && first <= Array.length lines then
                 let last = min last (Array.length lines) in
                 List.init (last - first + 1)
                   (fun offset ->
                     let line_number = first + offset in
                     (line_number, lines.(line_number - 1)))
               else [])

let print_source_location session =
  List.iter
    (fun (line_number, line) -> Printf.printf "  %d | %s\n" line_number line)
    (source_location_lines session)

let line_has_call_opcode line =
  let instruction =
    match String.index_opt line ';' with
    | None -> line
    | Some comment -> String.sub line 0 comment
  in
  Str.split (Str.regexp "[ \t]+") (String.trim instruction)
  |> List.exists (String.equal "call")

let location_is_call session =
  List.exists (fun (_, line) -> line_has_call_opcode line) (source_location_lines session)

let advance side session ~command tree =
  let single = command = StepITree in
  let until_call = command = StepCall in
  let old_globals = session.globals in
  let old_stack = session.stack in
  let old_location = session.location in
  publish_observers session;
  let first_node = describe_next_node session in
  let rec advance_from count tree =
    match Interpreter.single_step tree with
    | Either.Right result ->
        session.tree <- None;
        capture_observers session;
        if not single then Printf.printf "Advanced %d ITree transition(s).\n" (count + 1);
        report_step first_node session;
        report_result side result;
        report_introduced old_globals old_stack session
    | Either.Left next ->
        let count = count + 1 in
        session.tree <- Some next;
        let boundary = next_node_is_boundary next in
        capture_observers session;
        let changed = state_changed old_globals old_stack old_location session in
        let reached_call = until_call && location_is_call session in
        let limit_reached = count >= step_limit in
        if single || boundary || reached_call || (not until_call && changed) || limit_reached
        then begin
          if single then report_step first_node session
          else begin
            Printf.printf "Advanced %d ITree transition(s).\n" count;
            report_step (describe_next_node session) session;
            print_source_location session;
            if limit_reached && not boundary && not reached_call then
              Printf.printf
                "Stopped after %d transitions without reaching the requested boundary.\n"
                step_limit
          end;
          report_introduced old_globals old_stack session
        end
        else advance_from count next
  in
  advance_from 0 tree

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
  | Some (Examine (local, count) as command) ->
      let session = match focus with Left -> left | Right -> right in
      examine_memory session local count;
      command_loop left right focus (Some command)
  | Some (Step | StepITree | StepCall as command) ->
      let side, session =
        match focus with Left -> ("Left", left) | Right -> ("Right", right)
      in
      (match session.tree with
       | None -> Printf.printf "%s program has already stopped.\n" side
       | Some tree -> advance side session ~command tree);
      command_loop left right focus (Some command)

(* [-skip-init], for one side: get to the code under test before the first
   prompt, instead of making the user step through the global environment twice
   over, once per side.

   This goes through the observers like every other step, and one side at a time,
   because the debugger observers are process-wide mutable state that the two
   sides take turns owning: skipping the left side leaves the observers holding
   the left side's post-initialization state, which is why the right side has to
   publish its own before it may advance. *)
let skip_initialization side ~(frames : int) session =
  match session.tree with
  | None -> ()
  | Some tree -> (
      publish_observers session ;
      match Interpreter.skip_initialization ~frames tree with
      | Either.Left tree ->
          session.tree <- Some tree ;
          capture_observers session ;
          Printf.printf "%s program is at %s, past initialization.\n" side
            (show_location session.location)
      | Either.Right result ->
          session.tree <- None ;
          capture_observers session ;
          Printf.printf "%s program stopped before reaching its entry.\n" side ;
          report_result side result )

let interleave_itrees ~(left_skip : int option) ~(right_skip : int option)
    ~left_source ~right_source left right =
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
  let initial_location_state =
    LLVMEvents.printer_object.printer_get_loc_state ()
  in
  let initial_memory =
    (Memory0.memory_object Interpreter.params).memory_get ()
  in
  let left =
    { tree = Some left;
      source_path = left_source;
      memory = initial_memory;
      stack = initial_stack;
      globals = initial_globals;
      location_state = initial_location_state;
      location = initial_location;
    }
  in
  let right =
    { tree = Some right;
      source_path = right_source;
      memory = initial_memory;
      stack = initial_stack;
      globals = initial_globals;
      location_state = initial_location_state;
      location = initial_location;
    }
  in
  Option.iter (fun frames -> skip_initialization "Left" ~frames left) left_skip;
  Option.iter (fun frames -> skip_initialization "Right" ~frames right) right_skip;
  command_loop left right Left None

(* Each side carries its own entry, buffers and link files: the two programs are
   resolved independently, so they may start from different functions with
   different arguments and different memory set up for them. *)
let interleave args shared_links left_side right_side =
  Out_channel.set_buffered stdout false;
  Out_channel.set_buffered stderr false;
  let left, left_entry, left_skip = build_itree args shared_links left_side in
  let right, right_entry, right_skip = build_itree args shared_links right_side in
  (* The label is the manifest's [name:] when there is one, and the basename of
     the program otherwise, in which case there is no point in printing both. *)
  let describe side entry =
    let program = Filename.basename side.path in
    let program =
      if side.label = program then program else Printf.sprintf "%s (%s)" side.label program
    in
    match entry with
    | None -> program
    | Some entry -> Printf.sprintf "%s, from %s" program entry
  in
  Printf.printf " Left file: %s\n" (describe left_side left_entry);
  Printf.printf "Right file: %s\n" (describe right_side right_entry);
  interleave_itrees ~left_skip ~right_skip
    ~left_source:left_side.path ~right_source:right_side.path left right;
