(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

(* Vellvm top level user interface ------------------------------------------ *)
open VellvmLib
open Arg

(* Main flags for controlling driver behavior ------------------------------- *)
let interpret = ref false
let debugger = ref false
let interleaved_interpret = ref None
let entry_function = ref None
let entry_function_left = ref None
let entry_function_right = ref None
let entry_args = ref None
let entry_args_left = ref None
let entry_args_right = ref None
let entry_buffers = ref []
let entry_buffers_left = ref []
let entry_buffers_right = ref []
let optimize = ref false
let emit_llvm = ref false

(* Linking ------------------------------------------------------------------ *)

(* Files linked by reference to a directory via -L *)
let link_files : TopLevel.ll_toplevel_entities list ref = ref []

(* Files linked into one side of an interleaving only, via -link-left and
   -link-right. This is where a hand-written harness goes when the generated one
   is not enough: the two sides usually need different setup code, and -l/-L link
   into both. *)
let link_files_left : TopLevel.ll_toplevel_entities list ref = ref []
let link_files_right : TopLevel.ll_toplevel_entities list ref = ref []

let add_link_ast ast =
  link_files := ast :: !link_files

let link_file path =
  let _ = Platform.verb @@ Printf.sprintf "* linking file: %s" path in
  add_link_ast (IO.parse_file path)

let link_file_into side name path =
  let _ = Platform.verb @@ Printf.sprintf "* linking file (%s only): %s" name path in
  side := IO.parse_file path :: !side

(* Include all .ll files from the given directory *)
let link_dir dir =
  let files = Platform.ll_files_of_dir dir in
  List.iter link_file files


(* Optimization / Transformation pipeline ----------------------------------- *)
let transform
    (prog :
      ( LLVMAst.typ
      , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
      LLVMAst.toplevel_entity
      list ) :
    ( LLVMAst.typ
    , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
    LLVMAst.toplevel_entity list =
  prog


(* Processiing of one file -------------------------------------------------- *)
let process_file path =
  let basename, _ = Platform.path_to_basename_ext path in
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  (* Parse the file *)
  let ll_ast = IO.parse_file path in
  (* Optimize it *)
  let ll_opt = if !optimize then begin
                   Platform.verb @@ Printf.sprintf " - optimizing file: %s\n" path;
                   transform ll_ast
                 end
               else ll_ast
  in
  let _  =
    if !emit_llvm then
      (* Output the resulting processed file *)
      let vll_file = Platform.gen_name !Platform.output_path basename ".v.ll" in
      let _ = Platform.verb @@ Printf.sprintf " - emitting   file: %s\n" vll_file in
      IO.output_file vll_file ll_opt
    else ()
  in
  (* Add the result to the link files list *)    
  let _ = add_link_ast ll_opt in
  ()

let command_line_args = ref ["todo"]

let test_file file = Test.test_file !link_files file

let test_all () = Test.test_all !link_files

let test_dir dir = Test.test_dir !link_files dir

let args =
  [ ( "-test"
    , Unit test_all
    , "run comprehensive test suite\n\
       \tequivalent to running:\n\
       \t -test-pp-dir ../tests, then\n\
       \t -test-dir ../tests"
    )

  ; ( "-test-file"
    , String test_file
    , "run the assertions in a given file"
    )

  ; ( "-test-dir"
    , String test_dir
    , "run all .ll files in the given directory"
    )

  ; ( "-test-pp-file"
    , String FrontendTest.test_pp_file
    , "run the parsing/pretty-printing tests on the given .ll"
    )
  ; ( "-test-pp-dir"
    , String FrontendTest.test_pp_dir
    , "run the parsing/pretty-printing tests on all .ll files in the given \
       directory"
    )

  ; ( "-print-ast"
    , String FrontendTest.ast_pp_file
    , "run the parsing on the given .ll file and write its internal ast \
       representation to a .v.ast file in the output directory."
    )

  ; ( "-args"
    , Rest_all (fun args -> command_line_args := args)
    , "interpret the rest of the command line arguments as 'argv' for 
       EACH .ll file that vellvm interprets. Note that all strings after 
       -args will be interpreted as members of argv, and not arguments to vellvm."
    )

  ; ( "-O"
    , Set optimize
    , "transform the source")
  ; ( "-emit-llvm"
    , Set emit_llvm
    , "save the resulting .ll as .v.ll in the output directory")
  ; ( "-op"
    , Set_string Platform.output_path
    , "set the path to the output files directory  [default='output']" )

  ; ( "-l"
    , String link_file
    , "link one .ll file" )
  ; ( "-L"
    , String link_dir
    , "link all .ll files in the given directory" )

  ; ( "-interpret"
    , Set interpret
    , "interpret ll program starting from 'main'"
    )
  ; ( "-i"
    , Set interpret
    , "interpret ll program starting from 'main' (same as -interpret)"
    )

  ; ( "-debug"
    , Set Interpreter.debug_flag
    , "enable debugging trace output"
    )

  ; ( "-debugger"
    , Set debugger
    , "debug an ll program (use `h` at prompt to get help)"
    )

  ; ( "-interleave"
    , Tuple
        [ String (fun left -> interleaved_interpret := Some (left, ""))
        ; String
            (fun right ->
              match !interleaved_interpret with
              | Some (left, "") -> interleaved_interpret := Some (left, right)
              | _ -> assert false)
        ]
    , "interleave two ll programs (driver stub)"
    )

  ; ( "-entry"
    , String (fun name -> entry_function := Some name)
    , "start BOTH programs from the given function instead of 'main'\n\
       \tonly supported by -interleave, and the function must be defined in\n\
       \tboth programs. Globals are still allocated and initialized, but\n\
       \tnothing that 'main' would have set up is: no argv (-args is ignored),\n\
       \tempty heap. Without -entry-args, arguments default to zero/null.\n\
       \tIncompatible with -entry-left and -entry-right."
    )

  ; ( "-entry-left"
    , String (fun name -> entry_function_left := Some name)
    , "start the left program from the given function; must be paired with\n\
       \t-entry-right, and is incompatible with -entry"
    )

  ; ( "-entry-right"
    , String (fun name -> entry_function_right := Some name)
    , "start the right program from the given function; must be paired with\n\
       \t-entry-left, and is incompatible with -entry"
    )

  ; ( "-entry-args"
    , String (fun args -> entry_args := Some args)
    , "arguments for the entry of BOTH programs, as a comma-separated list of typed\n\
       \tLLVM literals, e.g. -entry-args 'i64 3, i8* null'.\n\
       \tWithout -entry-buffer these are built without touching memory, using the\n\
       \tsame syntax as the arguments of a call in an ASSERT directive and hence\n\
       \twith the same restrictions: pointers must be null, and aggregate types\n\
       \tmust be spelled out structurally, as in '{i32, i32} {i32 3, i32 4}'\n\
       \trather than '%pair {i32 3, i32 4}'.\n\
       \tWith -entry-buffer they become the arguments of a real call in the\n\
       \tgenerated harness, which lifts both restrictions: they may name buffers\n\
       \t(e.g. 'ptr %in, i32 5') and use the program's own type names."
    )

  ; ( "-entry-args-left"
    , String (fun args -> entry_args_left := Some args)
    , "arguments for the entry of the left program only, overriding -entry-args"
    )

  ; ( "-entry-args-right"
    , String (fun args -> entry_args_right := Some args)
    , "arguments for the entry of the right program only, overriding -entry-args"
    )

  ; ( "-entry-buffer"
    , String (fun buffer -> entry_buffers := buffer :: !entry_buffers)
    , "allocate memory before calling the entry of BOTH programs, and pass it by\n\
       \treference. May be repeated; each occurrence is\n\
       \t  -entry-buffer 'name : <type>'                  (allocate only)\n\
       \t  -entry-buffer 'name : <type> = <initializer>'  (allocate and store)\n\
       \tas in -entry-buffer 'in : [5 x i32] = [i32 1, i32 2, i32 3, i32 4, i32 5]'.\n\
       \tRefer to a buffer as '%name' in -entry-args, and in the initializer of\n\
       \tany other buffer: every buffer is allocated before any is initialized,\n\
       \tso the references may go in either direction, or in a cycle.\n\
       \tGiving a buffer switches that side to running through a generated\n\
       \tharness (see -show-harness) instead of calling the entry directly."
    )

  ; ( "-entry-buffer-left"
    , String (fun buffer -> entry_buffers_left := buffer :: !entry_buffers_left)
    , "a buffer for the left program only; may be repeated. If any is given, the\n\
       \tleft program uses these buffers instead of the -entry-buffer ones"
    )

  ; ( "-entry-buffer-right"
    , String (fun buffer -> entry_buffers_right := buffer :: !entry_buffers_right)
    , "a buffer for the right program only; may be repeated. If any is given, the\n\
       \tright program uses these buffers instead of the -entry-buffer ones"
    )

  ; ( "-link-left"
    , String (link_file_into link_files_left "left")
    , "link one .ll file into the left program only; may be repeated. Unlike -l,\n\
       \twhich links into both, this is where a hand-written harness for one side\n\
       \tgoes: define a function there and name it with -entry-left"
    )

  ; ( "-link-right"
    , String (link_file_into link_files_right "right")
    , "link one .ll file into the right program only; may be repeated"
    )

  ; ( "-show-harness"
    , Set Entry.show_harness
    , "print the harness generated from -entry-buffer for each side"
    )

  ; ( "-v"
    , Set Platform.verbose
    , "enables more verbose compilation output"
    )
 ]

let main () =
  (* Files specified directly on the command line *)
  Platform.configure () ;
  Printf.printf "(* -------- Vellvm Test Harness -------- *)\n%!" ;
  try
    Arg.parse args process_file
      "USAGE: ./vellvm [options] <files>\n" ;
    let prog = TopLevel.link_all !link_files [] in
    (* The two programs are entered independently. The entry itself is chosen
       either once for both sides with -entry or per side with
       -entry-left/-entry-right, and the two schemes are mutually exclusive.
       Arguments, in contrast, layer: a side's own -entry-args-<side> wins over
       the -entry-args shared by both, which in turn wins over defaults built
       from that side's own prototype. *)
    let left_name, right_name =
      match (!entry_function, !entry_function_left, !entry_function_right) with
      | Some _, Some _, _ | Some _, _, Some _ ->
          failwith "-entry is incompatible with -entry-left and -entry-right"
      | Some shared, None, None -> (Some shared, Some shared)
      | None, (Some _ as left), (Some _ as right) -> (left, right)
      | None, Some _, None | None, None, Some _ ->
          failwith
            "-entry-left and -entry-right must be given together (use -entry to \
             enter both programs at the same function)"
      | None, None, None -> (None, None)
    in
    let entry_of name side_args side_buffers =
      match name with
      | None -> None
      | Some name ->
          let args = if Option.is_some side_args then side_args else !entry_args in
          let buffers = if side_buffers <> [] then side_buffers else !entry_buffers in
          (* The flags accumulate in reverse; the buffers keep the order they
             were given in, which is the order they are allocated in. *)
          Some Entry.{name; args; buffers = List.rev buffers}
    in
    let left_entry = entry_of left_name !entry_args_left !entry_buffers_left in
    let right_entry = entry_of right_name !entry_args_right !entry_buffers_right in
    if Option.is_none left_entry
       && (List.exists Option.is_some [!entry_args; !entry_args_left; !entry_args_right]
          || List.exists (( <> ) []) [!entry_buffers; !entry_buffers_left; !entry_buffers_right])
    then
      failwith
        "-entry-args and -entry-buffer require -entry, or -entry-left and -entry-right" ;
    if Option.is_some left_entry && not (Option.is_some !interleaved_interpret) then
      failwith
        "-entry (and -entry-left/-entry-right) is currently only supported by -interleave" ;
    if (!link_files_left <> [] || !link_files_right <> [])
       && not (Option.is_some !interleaved_interpret)
    then failwith "-link-left and -link-right are only supported by -interleave" ;
    if Option.is_some !interleaved_interpret then
      match !interleaved_interpret with
      | Some (left, right) ->
          Interleave.interleave !command_line_args !link_files
            {Interleave.path = left; entry = left_entry; links = List.rev !link_files_left}
            {Interleave.path = right; entry = right_entry; links = List.rev !link_files_right}
      | None -> assert false
    else if !interpret then
      match Interpreter.interpret !command_line_args prog with
      | Ok dv ->
         Printf.printf "Program terminated with: %s\n" (Interpreter.string_of_dvalue dv)
      | Error e -> failwith (Result.string_of_exit_condition e)
    else if !debugger then
      (Interpreter.debug_flag := true;
       match Debugger.vellvm_debugger !command_line_args prog with
       | Ok dv ->
          Printf.printf "Program terminated with: %s\n" (Interpreter.string_of_dvalue dv)
       | Error e -> failwith (Result.string_of_exit_condition e))
  with
  | Assert.Ran_tests true -> exit 0
  | Assert.Ran_tests false -> exit 1

;; main ()
