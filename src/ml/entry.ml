(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 ---------------------------------------------------------------------------- *)

(** Resolving a user-specified entry point.

    The Rocq semantics already takes the entry point as a parameter:
    [TopLevel.interpreter_gen] is given a return type, a [function_id] and an
    itree producing the argument [dvalue]s, and [TopLevel.interpreter] is just
    its specialization to @main with `argv` built by [build_main_args].
    Initialization of the global environment happens in [denote_vellvm] before
    the entry is ever read, so globals are allocated and initialized whichever
    entry we pick.

    This module recovers the signature of an arbitrary entry from the program's
    own prototype, and gets us to that entry in one of two ways.

    - Directly, when the arguments are all scalars: the argument list written by
      the user is turned into the [dvalue]s that [interpreter_gen] expects. This
      is cheap but purely functional, so a pointer argument can only be null.

    - Through a *harness*, as soon as a buffer is requested (with [-entry-buffer]
      or a manifest's [buffer:], see {!Manifest}): we synthesize a nullary LLVM
      function that allocates the requested buffers, initializes them, calls the
      real entry and returns its result, then enter the program at that harness
      instead. Nothing here interprets the buffers itself --
      they are emitted as the [alloca]/[store] pair they are written as and run
      through the real parser and the real semantics. *)

open VellvmLib
open LLVMAst
module DV = DynamicValues

(** A request as the user wrote it, and where they wrote it: the text of an
    argument list or of a buffer, plus a label naming the flag or the manifest
    line it came from. Only error messages read [origin], but they need it: the
    same request can come from [-entry-buffer] or from line 12 of a [.vellvm]
    manifest, and a message that names the wrong one is worse than useless. *)
type written = {text: string; origin: string}

(** An entry point as requested by the user: the name of the function, the
    arguments as written (a comma-separated list of typed LLVM literals, e.g.
    ["i64 3, i8* null"]), and the buffers to allocate before the call (see
    [parse_buffer] for their syntax). [None] arguments means "make up default
    values from the prototype"; no buffers means the entry is called directly,
    without a harness. [origin] is where the entry itself was requested. *)
type spec = {name: string; origin: string; args: written option; buffers: written list}

(** The entry point resolved against one particular program. [prog] is the
    program to actually run: the one passed to [resolve], with the generated
    harness linked in when there is one. *)
type t =
  { entry: function_id
  ; ret_typ: DynamicTypes.dtyp
  ; arg_dvalues: DV.dvalue list
  ; prog: TopLevel.ll_toplevel_entities
  ; frames_to_entry: int
        (** How many stack frames below the itree's starting point the function
            the user asked for sits: one when [entry] is that function, and two
            when [entry] is a generated harness that calls it. This is what
            [Interpreter.skip_initialization] needs in order to stop at the
            requested entry rather than at the harness that sets up its
            arguments. *)
  ; description: string }

(** Print the harness we generate, for each side, on stdout. Set by
    [-show-harness]; the generated module is the whole story of what a
    [-entry-buffer] request means, so it is worth being able to read it. *)
let show_harness = ref false

(** The names the harness introduces are all under one reserved prefix, so as not
    to capture anything the program under test might define, and so that a buffer
    name can be rejected for colliding with them. *)
let harness_prefix = "__vellvm_"

let harness_function = harness_prefix ^ "harness"

let harness_result = harness_prefix ^ "result"

let show_dtyp dtyp = Camlcoq.camlstring_of_coqstring (ShowAST.show_dtyp dtyp)

let show_typ typ = Llvm_printer.string_of_typ typ

(* Tolerate both `-entry f` and `-entry @f`. *)
let function_id_of_name name =
  let name =
    if String.length name > 0 && name.[0] = '@' then
      String.sub name 1 (String.length name - 1)
    else name
  in
  (name, Name (Camlcoq.coqstring_of_camlstring name))

(** The [typ]-level prototype of [entry] among the definitions of [prog], along
    with the program's type definitions.

    We deliberately look before [convert_types]: at the dtyp level a function
    type is erased to [DTYPE_Pointer] (see [typ_to_dtyp_base_option]), so a
    dtyp-level prototype no longer records the signature. *)
let prototype ~(context : string) ~(origin : string)
    (prog : TopLevel.ll_toplevel_entities) (entry : function_id) =
  let mcfg : typ CFG.mcfg =
    CFG.mcfg_of_tle (TopLevel.link TopLevel.coq_PREDEFINED_FUNCTIONS prog)
  in
  let has_name (d : (typ, typ CFG.cfg) definition) = d.df_prototype.dc_name = entry in
  match List.find_opt has_name mcfg.CFG.m_definitions with
  | Some d -> (mcfg.CFG.m_type_defs, d.df_prototype)
  | None ->
      failwith
        (Printf.sprintf
           "%s: %s: no definition of %s (a declaration is not enough, the entry needs a body)"
           context origin (Interpreter.string_of_function_id entry) )

(** Return type, parameter types and vararg flag of a prototype, in surface
    syntax. The harness is emitted as text, so it needs the types as the parser
    gave them rather than their dtyp erasures. *)
let signature ~(context : string) (proto : typ declaration) =
  match proto.dc_type with
  | TYPE_Function (ret, params, vararg) -> (ret, params, vararg)
  | _ ->
      failwith
        (Printf.sprintf "%s: the prototype of %s is not a function type" context
           (Interpreter.string_of_function_id proto.dc_name) )

(** The canonical default value of a type: zero for integers and floats, null
    for pointers, pointwise for aggregates. This is the same choice the
    executable [DrawE] handler makes for under-defined values. *)
let default_dvalue ~(context : string) dtyp =
  try Assertion.ocaml_of_EOU (DV.default_dvalue_of_dtyp Interpreter.params dtyp)
  with Failure msg ->
    failwith
      (Printf.sprintf "%s: no default value for a parameter of type %s: %s" context
         (show_dtyp dtyp) msg )

(** Parse the user's argument list by handing a synthetic call to the same
    parser the ASSERT directives use, and return the arguments as typed
    expressions. Going through the real grammar means the commas inside
    aggregate literals (e.g. [<2 x i1> <i1 0, i1 1>]) are handled for us. *)
let parse_call_args ~(context : string) (name : string) (request : written) =
  (* The callee's type in this synthetic call is never read: we only want the
     argument list back. We use a placeholder because [test_call] parses the
     callee as a [texp], and [typ] has no production for a bare `void`. *)
  let call = Printf.sprintf "call i64 @%s(%s)" name request.text in
  let instr =
    try Llvm_lexer.parse_test_call (Lexing.from_string call)
    with e ->
      failwith
        (Printf.sprintf "%s: %s: ill-formed argument list %S: %s" context request.origin
           request.text (Printexc.to_string e) )
  in
  match instr with
  | INSTR_Call (_, args, _, _) -> List.map fst args
  | _ ->
      failwith
        (Printf.sprintf "%s: %s: %S is not an argument list" context request.origin
           request.text )

let check_arity ~(context : string) (entry : function_id) params vararg args =
  let expected = List.length params and got = List.length args in
  if got < expected || (got > expected && not vararg) then
    failwith
      (Printf.sprintf "%s: %s takes %d argument(s)%s, but %d were given" context
         (Interpreter.string_of_function_id entry)
         expected
         (if vararg then " plus varargs" else "")
         got )

(** * Buffers *)

(** A buffer as requested with [-entry-buffer] or a manifest's [buffer:]: a name
    to refer to it by, the type of the storage to allocate, and what to
    initialize it with.

    The type and the initializer are kept as the user's own text, so that what
    runs is what was written rather than a round trip through the printer, and so
    that a malformed request can be reported with the offending text quoted
    verbatim. [buf_exp] is the parsed initializer, which [emit_stores] needs in
    order to see the shape of an aggregate. *)
type buffer =
  { buf_name: string
  ; buf_typ: string
  ; buf_init: string option
  ; buf_exp: typ exp option
  ; buf_origin: string }

(* The characters LLVM allows in an unquoted identifier. *)
let is_identifier_char c =
  (c >= 'a' && c <= 'z')
  || (c >= 'A' && c <= 'Z')
  || (c >= '0' && c <= '9')
  || c = '.' || c = '_' || c = '$' || c = '-'

(* Tolerate both `b : ...` and `%b : ...`, the way [function_id_of_name]
   tolerates a leading `@`. *)
let buffer_name ~(context : string) (request : written) (name : string) =
  let name = String.trim name in
  let name =
    if String.length name > 0 && name.[0] = '%' then
      String.sub name 1 (String.length name - 1)
    else name
  in
  if name = "" then
    failwith
      (Printf.sprintf "%s: %s: buffer %S has an empty name" context request.origin
         request.text ) ;
  String.iter
    (fun c ->
      if not (is_identifier_char c) then
        failwith
          (Printf.sprintf "%s: %s: buffer %S: %C is not allowed in a buffer name" context
             request.origin request.text c ) )
    name ;
  if String.starts_with ~prefix:harness_prefix name then
    failwith
      (Printf.sprintf "%s: %s: buffer %S: %s is reserved for the harness's own locals"
         context request.origin request.text harness_prefix ) ;
  name

(** Parse one [-entry-buffer] request: [name : type] to only allocate the
    storage, or [name : type = initializer] to also store into it.

    The two halves cannot be validated separately: the LLVM grammar reads an
    aggregate literal relative to its type (the [global_decl] rule applies the
    type to the expression, which is how [[i32 1, i32 2]] becomes an [EXP_Array]
    over the right element type), so we check them together, by parsing a
    throwaway global. That the probe is a whole toplevel entity is what makes it
    reject trailing junk: the [texp] production it would otherwise be natural to
    use is not anchored at [EOF], so it would quietly accept -- and drop -- the
    second half of a mistake like ['p : %node = %node { i32 1, ptr null }'].
    When there is no initializer we probe the type with `undef`, since the
    grammar has no production for a type on its own. *)
let parse_buffer ~(context : string) (request : written) =
  let source = request.text in
  let name, rest =
    match String.index_opt source ':' with
    | Some i -> (String.sub source 0 i, String.sub source (i + 1) (String.length source - i - 1))
    | None ->
        failwith
          (Printf.sprintf
             "%s: %s: buffer %S is not of the form 'name : <type>' or \
              'name : <type> = <initializer>'"
             context request.origin source )
  in
  let buf_name = buffer_name ~context request name in
  let typ_source, init_source =
    match String.index_opt rest '=' with
    | Some i -> (String.sub rest 0 i, Some (String.sub rest (i + 1) (String.length rest - i - 1)))
    | None -> (rest, None)
  in
  let buf_typ = String.trim typ_source in
  let buf_init = Option.map String.trim init_source in
  if buf_typ = "" then
    failwith
      (Printf.sprintf "%s: %s: buffer %S has no type" context request.origin source) ;
  if buf_init = Some "" then
    failwith
      (Printf.sprintf
         "%s: %s: buffer %S has an empty initializer (drop the '=' to only \
          allocate the storage)"
         context request.origin source ) ;
  let probe =
    Printf.sprintf "@%sprobe = global %s %s" harness_prefix buf_typ
      (Option.value buf_init ~default:"undef")
  in
  let parsed =
    match
      try Llvm_lexer.parse (Lexing.from_string probe)
      with e ->
        failwith
          (Printf.sprintf "%s: %s: ill-formed buffer %S: %s" context request.origin source
             (Printexc.to_string e) )
    with
    | [TLE_Global g] -> g.g_exp
    | _ ->
        failwith
          (Printf.sprintf "%s: %s: ill-formed buffer %S" context request.origin source)
  in
  (* With no initializer what was parsed is the `undef` we made up, not
     something the user asked to be stored. *)
  let buf_exp = if Option.is_some buf_init then parsed else None in
  {buf_name; buf_typ; buf_init; buf_exp; buf_origin = request.origin}

(* Two buffers of the same name would emit the same local twice; catch it here
   rather than in the generated harness, where the error would be obscure. *)
let check_buffer_names ~(context : string) (buffers : buffer list) =
  let rec check seen = function
    | [] -> ()
    | b :: rest ->
        if List.mem b.buf_name seen then
          failwith
            (Printf.sprintf "%s: %s: buffer %s is requested more than once" context
               b.buf_origin b.buf_name )
        else check (b.buf_name :: seen) rest
  in
  check [] buffers

(** The elements of an initializer that has to be stored element by element
    rather than as one aggregate, or [None] if it can be stored whole.

    A plain struct always forces the split, because it is the one aggregate whose
    fields are padded, and Vellvm does not agree with itself about where that
    padding goes: a whole-aggregate [store] of [{i32, ptr}] writes the pointer at
    byte 8, while [getelementptr {i32, ptr}, ptr %p, i32 0, i32 1] -- what a
    clang- or rustc-derived program reads it back with -- computes byte 4.
    ([handle_gep_h] in Operations/Gep.v pads the fields it skips over but not the
    field it lands on, whereas [Sizeof_dtyp] pads all of them, which is also the
    layout [alloca] reserves room for.) Storing field by field means the harness
    addresses memory the same way the program under test does, whichever offset
    is the right one, so it stays correct if that is ever reconciled.

    Arrays, vectors and packed structs are laid out identically by both, so they
    are split only to reach a struct nested inside one. *)
let rec split_initializer (exp : typ exp) =
  let contains_split elts =
    if List.exists (fun (_, e) -> split_initializer e <> None) elts then Some elts else None
  in
  match exp with
  | EXP_Struct elts -> Some elts
  | EXP_Packed_struct elts | EXP_Array (_, elts) | EXP_Vector (_, elts) -> contains_split elts
  | _ -> None

(** The local naming the address of one element of a buffer. The path is the
    element's position, so [%__vellvm_p_1_0] is field 0 of field 1 of [%p]. *)
let field_pointer (b : buffer) (path : int list) =
  Printf.sprintf "%%%s%s%s" harness_prefix b.buf_name
    (String.concat "" (List.map (Printf.sprintf "_%d") path))

(** Emit the [store]s that initialize one buffer, descending into the initializer
    as far as [split_initializer] says to and no further. [path] is the position
    of [exp] within the buffer, and [source] is [exp] as a typed operand: at the
    root that is the user's own text, and below it we print from the parse, since
    there is no text for a part of what they wrote. *)
let rec emit_stores out (b : buffer) ~(path : int list) ~(source : string) (exp : typ exp) =
  let add fmt = Printf.ksprintf (Buffer.add_string out) fmt in
  match split_initializer exp with
  | Some elts ->
      List.iteri
        (fun i (t, e) ->
          let source = Printf.sprintf "%s %s" (show_typ t) (Llvm_printer.string_of_exp e) in
          emit_stores out b ~path:(path @ [i]) ~source e )
        elts
  | None -> (
    match path with
    | [] -> add "  store %s, ptr %%%s\n" source b.buf_name
    | _ ->
        (* The leading 0 steps over the buffer itself: [%p] is the address of one
           object, and the rest of the path indexes into it. *)
        let dest = field_pointer b path in
        add "  %s = getelementptr %s, ptr %%%s, i32 0%s\n" dest b.buf_typ b.buf_name
          (String.concat "" (List.map (Printf.sprintf ", i32 %d") path)) ;
        add "  store %s, ptr %s\n" source dest )

(** The harness: allocate every buffer, then initialize them, then call the
    entry.

    The two phases are kept separate on purpose, and for the same reason
    [build_global_environment] allocates all of a module's globals before
    initializing any of them: with every pointer already in scope by the time
    the first [store] runs, a buffer's initializer may mention any other buffer
    regardless of the order they were given in, including cyclically. *)
let harness_source ~(entry_name : string) ~(ret : typ) ~(buffers : buffer list)
    ~(args : string) =
  let out = Buffer.create 512 in
  let add fmt = Printf.ksprintf (Buffer.add_string out) fmt in
  let ret_source = show_typ ret in
  add "define %s @%s() {\n" ret_source harness_function ;
  List.iter (fun b -> add "  %%%s = alloca %s\n" b.buf_name b.buf_typ) buffers ;
  List.iter
    (fun b ->
      match (b.buf_init, b.buf_exp) with
      | Some init, Some exp ->
          emit_stores out b ~path:[]
            ~source:(Printf.sprintf "%s %s" b.buf_typ init)
            exp
      | _ -> () )
    buffers ;
  ( match ret with
  | TYPE_Void ->
      add "  call void @%s(%s)\n" entry_name args ;
      add "  ret void\n"
  | _ ->
      add "  %%%s = call %s @%s(%s)\n" harness_result ret_source entry_name args ;
      add "  ret %s %%%s\n" ret_source harness_result ) ;
  add "}\n" ;
  Buffer.contents out

(* The harness goes through the same parser as a file on the command line, and
   is given a filename so that locations reported inside it are legible. *)
let parse_harness ~(context : string) (source : string) =
  let lexbuf = Lexing.from_string source in
  IO.reset_lexbuf (Printf.sprintf "<harness:%s>" context) 1 lexbuf ;
  try Llvm_lexer.parse lexbuf
  with e ->
    failwith
      (Printf.sprintf "%s: the generated harness does not parse (%s):\n%s" context
         (Printexc.to_string e) source )

(** * Resolution *)

let describe_direct ret_typ entry arg_dvalues =
  Printf.sprintf "%s %s(%s)" (show_dtyp ret_typ)
    (Interpreter.string_of_function_id entry)
    (String.concat ", " (List.map Interpreter.string_of_dvalue arg_dvalues))

let describe_harness ret entry_name buffers args =
  Printf.sprintf "@%s() with %s, calling %s @%s(%s)" harness_function
    (String.concat ", " (List.map (fun b -> "%" ^ b.buf_name) buffers))
    (show_typ ret) entry_name args

(** Resolve [spec] against one linked program. [context] identifies the program
    in error messages. *)
let resolve ~(context : string) (prog : TopLevel.ll_toplevel_entities) (spec : spec) : t =
  let name, entry = function_id_of_name spec.name in
  let type_defs, proto = prototype ~context ~origin:spec.origin prog entry in
  let ret, params, vararg = signature ~context proto in
  let ret_typ = TypToDtyp.typ_to_dtyp type_defs ret in
  match spec.buffers with
  | [] ->
      let arg_dvalues =
        match spec.args with
        | Some request ->
            List.map Assertion.texp_to_dvalue (parse_call_args ~context name request)
        | None ->
            List.map
              (fun t -> default_dvalue ~context (TypToDtyp.typ_to_dtyp type_defs t))
              params
      in
      check_arity ~context entry params vararg arg_dvalues ;
      { entry
      ; ret_typ
      ; arg_dvalues
      ; prog
      ; frames_to_entry = 1
      ; description = describe_direct ret_typ entry arg_dvalues }
  | buffer_requests ->
      let buffers = List.map (parse_buffer ~context) buffer_requests in
      check_buffer_names ~context buffers ;
      let request =
        Option.value spec.args ~default:{text = ""; origin = spec.origin}
      in
      (* The arguments are spliced into the harness rather than evaluated here,
         but they still have to fit the entry, and a bad argument list gives a
         much better error from the synthetic call than from the harness. *)
      check_arity ~context entry params vararg (parse_call_args ~context name request) ;
      let source = harness_source ~entry_name:name ~ret ~buffers ~args:request.text in
      if !show_harness then
        Printf.printf "(* generated harness for %s *)\n%s" context source ;
      let harness = parse_harness ~context source in
      let _, harness_entry = function_id_of_name harness_function in
      { entry = harness_entry
      ; ret_typ
      ; arg_dvalues = []
      ; prog = TopLevel.link_all [harness] prog
      ; (* The harness's own frame, then the entry's. *)
        frames_to_entry = 2
      ; description = describe_harness ret name buffers request.text }

(** The [arg_gen] itree [interpreter_gen] expects. The arguments are produced
    purely, which is why a pointer argument passed this way can only be null:
    allocating a buffer for it would mean emitting [alloca]/[store] here, the
    way [TopLevel.allocate_args] does for `argv`. That is what the harness does
    instead, in LLVM rather than in OCaml; with a harness this list is empty,
    since the harness takes no parameters. *)
let arg_gen (resolved : t) =
  Monad.ret (Obj.magic ITreeDefinition.coq_Monad_itree) resolved.arg_dvalues

let interpreter (resolved : t) =
  TopLevel.interpreter_gen Interpreter.params resolved.ret_typ resolved.entry
    (arg_gen resolved) resolved.prog

let describe (resolved : t) = resolved.description
