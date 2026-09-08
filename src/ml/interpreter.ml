(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

module DV = DynamicValues

let iptr   = IPtrInfinite.coq_IPZ
let params = ParamsV.coq_ParamsV iptr
let pointer_v = Pointer0.coq_PointerV iptr

open LLVMEvents

open Format
open ITreeDefinition
open Result

let ocaml_str = Camlcoq.camlstring_of_coqstring

let string_of_dvalue (d : DV.dvalue) =
  ocaml_str (DV.show_dvalue params d)

let string_of_function_id id : string =
  LLVMAst.( match id with
  | Name n -> "@" ^ (Camlcoq.camlstring_of_coqstring n)
  | Anon z -> "@" ^ (Camlcoq.Z.to_string z)
  | Raw z ->  "_RAW_" ^  (Camlcoq.Z.to_string z)
  )

(* Converts `float` to a `string` at max precision. Both OCaml `printf` and
   `string_of_float` truncate and do not print all significat digits. *)
let string_of_float_full f =
  (* Due to the limited number of bits in the representation of doubles, the
     maximal precision is 324. See Wikipedia. *)
  let s = sprintf "%.350f" f in
  Str.global_replace (Str.regexp "0+$") "" s

let char_of_I8 x =
  char_of_int (Camlcoq.Z.to_int (Integers.unsigned (Camlcoq.P.of_int 8) x))

(* Converts a list of VellvmIntegers.Int8 values to OCaml string *)
let string_of_bytes (bytes : Integers.bit_int list) : bytes =
  List.map char_of_I8 bytes |> List.to_seq |> Bytes.of_seq

let debug_flag = ref false

(** Set by [-skip-init]: advance past the initialization of the global
    environment before handing the program to the debugger or the interleaver,
    rather than making the user step through it. *)
let skip_init = ref false

(** Print a debug message to stdout if the `debug_flag` is enabled.

    This is used to implement `debugE` events.
*)
let debug (msg : string) =
  if !debug_flag then Printf.printf "DEBUG: %s\n%!" msg

(** The `step` function walks through an itree and handles some
    remaining events.

    In particular, `step` handles `debugE`, `failE`, and
    `ExternalCallE` events, which are not handled by the
    TopLevel.interpreter function extracted from Coq.

    Calling `step` could either loop forever, return an error,
    or return the dvalue result returned from the itree.
 *)

let current_line = ref (Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()))

(* Mirrors [InterpretationStack.Res dvalue] = [FusedS * dvalue]. *)
type interp_state =
  (Memory.state * ((Stack.stack_frame * Stack.stack) * Global.global_env)) * DV.dvalue

let single_step (m : (__ coq_MCFGEbot, interp_state) itree)
    : ((__ coq_MCFGEbot, interp_state) itree,
       (DV.dvalue, exit_condition) result) Either.t =
  let open ITreeDefinition in
  match observe m with
  (* Internal steps compute as nothing *)
  | TauF x ->
     if !debug_flag then begin
         let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
         if loc_str <> !current_line then begin
             Printf.printf "%s\n%!" loc_str;
             current_line := loc_str
           end
     end;
     Either.left x
  (* SAZ: Could inspect the memory or stack here too. *)
  (* We finished the computation *)
  | RetF (_, v) -> Either.right (Ok v)
  (* The ExternalCallE effect *)
  | VisF (Sum.Coq_inl1 (ExternalCall (t, _, dvs)), _) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     let typ_str = Camlcoq.camlstring_of_coqstring (ReprAST.repr_dtyp t) in
     let args_str = string_of_int (List.length dvs) in
     Either.right
       (Error (UninterpretedCall
                 (Printf.sprintf "%s: Call with return type %s, %s dvalues."
                    loc_str typ_str args_str)))
  (* Still TODO: Integrate 2nd argument *)
  (* The IO_stdout effect *)
  | VisF (Sum.Coq_inl1 (IO_stdout bytes), k) ->
      let str = string_of_bytes bytes in
      output_bytes stdout str ;
      Either.left (k (Obj.magic ()))
  (* The IO_stderr effect *)
  | VisF (Sum.Coq_inl1 (IO_stderr bytes), k) ->
      let str = string_of_bytes bytes in
      output_bytes stderr str ;
      Either.left (k (Obj.magic ()))
  (* The OOME effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 _msg), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (OutOfMemory loc_str))

  (* LLVM Exception event *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _uv)), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (LLVMException loc_str))

  (* UBE event *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _msg))), _k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (UndefinedBehavior loc_str))

  (* The DebugE effect *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inl1 _msg)))), k) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     (debug loc_str;
      Either.left ((k (Obj.magic DV.DVALUE_None))))

  (* The FailureE effect is a failure *)
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 (Sum.Coq_inr1 _msg)))), _) ->
     let loc_str = Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ()) in
     Either.right (Error (Failed loc_str))

let rec step (m : (__ coq_MCFGEbot, interp_state) itree)
    : (DV.dvalue, exit_condition) result =
  match single_step m with
  | Either.Left x -> step x
  | Either.Right res -> res

let stack_depth () =
  List.length ((Stack.local_stack_object params).local_stack_get ())

(** Advance to the first instruction of the function the run starts from, past
    the global environment that [denote_vellvm] builds before the entry is ever
    called (and past `argv`, when the run starts at @main). A handful of globals
    is a few hundred ITree nodes, none of them the code under test, and stepping
    through them one node at a time is what [-skip-init] is for.

    "Now in the function we wanted" is read off the local stack rather than off
    the source location, because a frame being pushed is what entering a function
    means: the initialization runs in the frame that is already on the stack when
    the itree is built, so the entry's own frame is the first one pushed after it.
    [frames] is how many frames down the wanted function sits -- two rather than
    one when a generated harness stands between the itree's entry and the
    requested one, so that allocating and filling the buffers is skipped along
    with the globals (see [Entry.frames_to_entry]).

    Returns the program stopped at that point, or its result if it terminated
    first, which for a well-formed program means initialization itself failed. *)
let skip_initialization ~(frames : int) (m : (__ coq_MCFGEbot, interp_state) itree)
    : ((__ coq_MCFGEbot, interp_state) itree,
       (DV.dvalue, exit_condition) result) Either.t =
  let location () =
    Camlcoq.camlstring_of_coqstring (LLVMEvents.printer_object.printer_get_loc ())
  in
  let target = stack_depth () + frames in
  (* The frame is pushed before the function's first instruction is denoted, so
     stopping the moment [target] is reached would leave us reporting the caller's
     `call` as the current location (or, for the entry the itree itself starts at,
     the unknown location initialization ran under). Once the frame is there, take
     the few further steps until the location changes: that is the first
     instruction of the function beginning, and the position the debugger would
     report. It cannot already be that instruction's location, since the location
     only ever names something that has started running. *)
  let rec enter m =
    if stack_depth () >= target then start_of_body (location ()) m
    else
      match single_step m with
      | Either.Left next -> enter next
      | Either.Right result -> Either.Right result
  and start_of_body caller m =
    (* The depth check is a backstop: a body that returns without the location
       ever changing would otherwise run the rest of the program. *)
    if location () <> caller || stack_depth () < target then Either.Left m
    else
      match single_step m with
      | Either.Left next -> start_of_body caller next
      | Either.Right result -> Either.Right result
  in
  enter m

(** Interpret an LLVM program, returning a result that contains either the
    dvalue result returned by the LLVM program, or an error message.

    Note: programs consist of a non-empty list of blocks, represented by a
    tuple of a single block, and a possibly empty list of blocks.
 *)
let interpret
      (args : string list)
      (prog :
         ( LLVMAst.typ
         , LLVMAst.typ LLVMAst.block * LLVMAst.typ LLVMAst.block list )
           LLVMAst.toplevel_entity
           list )
    : (DV.dvalue, exit_condition) result =
  Out_channel.set_buffered stdout false;
  Out_channel.set_buffered stderr false;
  step (TopLevel.interpreter (List.map Camlcoq.coqstring_of_camlstring args) prog)
