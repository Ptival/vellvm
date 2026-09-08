(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 ---------------------------------------------------------------------------- *)

(** Run manifests.

    A [.vellvm] file describes one run of one LLVM program: the program, the
    files linked into it, and either the `argv` to give @main or the entry to call
    instead, with its arguments and the memory to allocate for them. It holds
    exactly what the [-entry]/[-entry-args]/[-entry-buffer]/[-link-*] flags hold,
    which stopped fitting on a command line as soon as two programs had to be set
    up differently:

    {v
      ; The Rust side of the rewrite comparison.
      name:    rust
      program: rewrite.ll             ; relative to this file
      link:    support/shims.ll

      entry:   @process
      arg:     ptr %in
      arg:     i64 5

      buffer in:  [5 x i32] = [i32 1, i32 2, i32 3, i32 4, i32 5]
      buffer out: %node = { i32 0, ptr null }
    v}

    The format is line-oriented, [key: value], because every interesting value
    here is LLVM source text: an initializer such as [c"hi\00"] or
    [%node { i32 3, ptr @target }] would have to be escaped in a format that
    quotes its strings, and these values are handed to the real LLVM parser
    exactly as written. Nothing here is unquoted or unescaped -- a value is the
    rest of its line, trimmed.

    - A line whose first non-blank character is [;] or [#] is a comment, and a
      blank line is ignored. There are no trailing comments: [;] is a comment in
      LLVM too, so it can only appear in a value as its own thing.
    - An indented line continues the value above it, joined with one space.
      Whitespace is insignificant in LLVM, so a long initializer can be folded
      over as many lines as it takes.
    - [key: <<TAG] instead takes every following line up to a line reading [TAG]
      as the value, verbatim, newlines included. That is how [harness:] carries a
      whole function.
    - [name:], [program:] and [entry:] may be given once. [link:], [harness:],
      [arg:], [argv:], [buffer:] and [include:] accumulate, in the order written:
      buffers are allocated in that order, and arguments are passed in it.
    - Paths are relative to the file the line is written in, so a manifest and
      the files it names move together.
    - [include: other.vellvm] splices another manifest in place. Its lists come in
      where the [include:] is, and a [name:]/[program:]/[entry:] in the including
      file wins over the included one -- which is how two sides share their
      buffers and differ in their entry.

    The keys, and the flags they stand for:

    {v
      name:      the label used for this side in the driver's own output
      program:   the .ll under test                       (required)
      link:      one .ll linked into it, repeatable       -link-left/-link-right
      harness:   LLVM source linked into it, repeatable   (usually a heredoc)
      entry:     the function to start from               -entry
      arg:       one argument, or a comma-separated list  -entry-args
      buffer n:  storage to allocate and pass by pointer  -entry-buffer
      argv:      whitespace-separated argv for @main      -args
      skip-init: begin stepping at the entry               -skip-init
      include:   another manifest to build on
    v}

    [argv:] and the entry keys are mutually exclusive: a run either starts at
    @main with an `argv`, or at a chosen entry with chosen arguments.

    [skip-init:] is the one key whose value is not LLVM text but a boolean
    ([true]/[false], [yes]/[no], [on]/[off]). It is also the one key that a flag
    may repeat rather than contradict: it changes nothing about what the program
    does, only where stepping starts, so [-skip-init] on the command line and
    [skip-init: yes] in a manifest add up instead of conflicting. *)

open VellvmLib

let extension = ".vellvm"

(** LLVM to link into the program: a file named by [link:], or the text of a
    [harness:]. Inline text keeps the manifest file and the line it started on, so
    that a parse error in a harness is reported where it was written. *)
type source =
  | Ll_file of string
  | Inline of {file: string; line: int; text: string}

(** How the program is entered. [Default_argv] is a whole-program run whose `argv`
    the manifest does not choose, leaving it to [-args]. *)
type run =
  | Default_argv
  | Argv of string list
  | From_entry of Entry.spec

type t =
  { label: string  (** [name:], or the basename of the program *)
  ; program: string
  ; links: source list
  ; run: run
  ; skip_init: bool
        (** [skip-init:]: advance this program to its entry before the first
            prompt, instead of stepping through the registration of its globals.
            Per program rather than per session, since that is what a manifest
            describes; [-skip-init] asks for it on every program at once. *) }

(** * Reading *)

(** Where a line came from. [depth] is the [include:] nesting depth of the file
    it is written in, which is what decides who wins when the same key is given
    in an included manifest and in the one including it: the smaller depth, the
    outer file. *)
type origin = {file: string; line: int; depth: int}

let where (o : origin) = Printf.sprintf "%s:%d" o.file o.line

let fail (o : origin) fmt =
  Printf.ksprintf (fun message -> failwith (Printf.sprintf "%s: %s" (where o) message)) fmt

(** One line, split into its key, the name after the key if there is one ([buffer
    in:]), and its value. [value_line] is the line the value's text starts on,
    which is the line itself, or the first line of a heredoc's body. *)
type entry = {key: string; arg: string option; value: string; value_line: int; origin: origin}

(* Keys that may be given once, and keys that accumulate. *)
let scalar_keys = ["entry"; "name"; "program"; "skip-init"]

let list_keys = ["arg"; "argv"; "buffer"; "harness"; "include"; "link"]

let known_keys = List.sort compare (scalar_keys @ list_keys)

let read_lines (path : string) =
  let channel =
    try open_in path
    with Sys_error message -> failwith (Printf.sprintf "cannot read %s: %s" path message)
  in
  let lines = ref [] in
  ( try
      while true do
        (* Tolerate CRLF: the trailing return would otherwise end up inside a
           value, where the LLVM parser would report it as a stray character. *)
        let line = input_line channel in
        let length = String.length line in
        let line =
          if length > 0 && line.[length - 1] = '\r' then String.sub line 0 (length - 1)
          else line
        in
        lines := line :: !lines
      done
    with End_of_file -> close_in channel ) ;
  Array.of_list (List.rev !lines)

let is_blank line = String.trim line = ""

let is_comment line =
  let trimmed = String.trim line in
  trimmed <> "" && (trimmed.[0] = ';' || trimmed.[0] = '#')

let is_indented line = line <> "" && (line.[0] = ' ' || line.[0] = '\t')

let resolve ~(relative_to : string) (path : string) =
  if Filename.is_relative path then Filename.concat (Filename.dirname relative_to) path
  else path

(* A path is worth checking here rather than where it is opened: by then the
   manifest line it was written on is out of reach, and a folded continuation line
   is easiest to see as the surprising path it produced. *)
let resolve_file ~(origin : origin) (path : string) =
  let resolved = resolve ~relative_to:origin.file path in
  if not (Sys.file_exists resolved) then fail origin "there is no file %s" resolved ;
  resolved

(* The key, and the one name a key is allowed to carry. Only [buffer] takes one:
   `buffer in: [5 x i32]` reads better than the `in : [5 x i32]` that
   [-entry-buffer] takes, which is still accepted as `buffer: in : [5 x i32]`. *)
let split_key (origin : origin) (field : string) =
  match Str.split (Str.regexp "[ \t]+") field with
  | [] -> fail origin "a line must begin with a key, as in 'program: prog.ll'"
  | [key] -> (key, None)
  | [key; name] -> (key, Some name)
  | key :: _ ->
      fail origin "the key %S is followed by more than one name (only 'buffer <name>:' takes one)"
        key

let check_key (origin : origin) (key : string) (arg : string option) =
  if not (List.mem key known_keys) then
    fail origin "unknown key %S (known keys: %s)" key (String.concat ", " known_keys) ;
  if Option.is_some arg && key <> "buffer" then
    fail origin "the key %S does not take a name; only 'buffer <name>:' does" key

(* The value of a `key: <<TAG` line: every line up to one reading TAG, verbatim.
   Returns the text, the line it starts on, and the line after the terminator. *)
let read_heredoc (origin : origin) (lines : string array) ~(tag : string) ~(start : int) =
  if tag = "" then
    fail origin "'<<' must be followed by a terminator, as in 'harness: <<LL'" ;
  let body = ref [] in
  let index = ref start in
  let terminated = ref false in
  while not !terminated do
    if !index >= Array.length lines then
      fail origin "the value opened with '<<%s' is never closed by a line reading %s" tag tag ;
    if String.trim lines.(!index) = tag then terminated := true
    else begin
      body := lines.(!index) :: !body ;
      incr index
    end
  done ;
  (String.concat "\n" (List.rev !body), start + 1, !index + 1)

(** Read one manifest into a flat list of entries, expanding [include:] where it
    is written so that every entry keeps its own file, line and depth. [stack] is
    the chain of files currently being included, for the cycle check. *)
let rec read_entries ~(stack : string list) ~(depth : int) (path : string) : entry list =
  (* The cycle check needs a name that does not depend on how the path was
     spelled; if the file does not exist, [read_lines] gives the better error. *)
  let canonical = try Unix.realpath path with Unix.Unix_error _ | Sys_error _ -> path in
  if List.mem canonical stack then
    failwith
      (Printf.sprintf "%s includes itself: %s" path
         (String.concat " -> " (List.rev (canonical :: stack)))) ;
  let lines = read_lines path in
  let entries = ref [] in
  (* Whether the last thing read was a line of *this* file, and so whether an
     indented line has something to continue: after an [include:] the head of
     [entries] belongs to the included file, which this file may not extend. *)
  let foldable = ref false in
  let index = ref 0 in
  while !index < Array.length lines do
    let line = lines.(!index) in
    let origin = {file = path; line = !index + 1; depth} in
    if is_blank line || is_comment line then incr index
    else if is_indented line then begin
      ( match !entries with
      | previous :: rest when !foldable ->
          entries := {previous with value = previous.value ^ " " ^ String.trim line} :: rest
      | _ -> fail origin "this line is indented, but there is no value above it to continue" ) ;
      incr index
    end
    else begin
      let field, value =
        match String.index_opt line ':' with
        | Some colon ->
            ( String.sub line 0 colon
            , String.trim (String.sub line (colon + 1) (String.length line - colon - 1)) )
        | None -> fail origin "expected 'key: value', but this line has no ':'"
      in
      let key, arg = split_key origin field in
      check_key origin key arg ;
      let value, value_line, next =
        if String.starts_with ~prefix:"<<" value then
          read_heredoc origin lines
            ~tag:(String.trim (String.sub value 2 (String.length value - 2)))
            ~start:(!index + 1)
        else (value, origin.line, !index + 1)
      in
      if value = "" then fail origin "the key %S has no value" key ;
      if key = "include" then begin
        let included = read_entries ~stack:(canonical :: stack) ~depth:(depth + 1)
            (resolve ~relative_to:path value) in
        entries := List.rev_append included !entries ;
        foldable := false
      end
      else begin
        entries := {key; arg; value; value_line; origin} :: !entries ;
        foldable := true
      end ;
      index := next
    end
  done ;
  List.rev !entries

(** * Building *)

(* A key that may be given once. An outer file overrides an included one, and a
   file that says the same thing twice is a mistake rather than an override. *)
let set_scalar (slot : (string * origin) option ref) (e : entry) =
  match !slot with
  | Some (_, previous) when previous.depth < e.origin.depth -> ()
  | Some (_, previous) when previous.depth = e.origin.depth ->
      fail e.origin "%S is already given at %s; it may only be given once" e.key (where previous)
  | _ -> slot := Some (e.value, e.origin)

(* Every other value is LLVM text, handed on unread; this one is a flag, so it is
   worth accepting the several ways a user might write it rather than insisting on
   one. *)
let boolean (origin : origin) (key : string) (value : string) =
  match String.lowercase_ascii value with
  | "true" | "yes" | "on" | "1" -> true
  | "false" | "no" | "off" | "0" -> false
  | _ ->
      fail origin "%S is a yes or no, and %S is neither (try true/false, yes/no or on/off)"
        key value

(* The origin of a request assembled from several lines, for error messages. *)
let origin_of_lines = function
  | [] -> ""
  | [(_, origin)] -> where origin
  | (_, first) :: rest ->
      let last = snd (List.nth rest (List.length rest - 1)) in
      Printf.sprintf "%s-%d" (where first) last.line

let build ~(path : string) (entries : entry list) : t =
  let name = ref None and program = ref None and entry_name = ref None in
  let skip_init = ref None in
  (* Every list is accumulated reversed and reversed once at the end, so that the
     order the user wrote is the order things are allocated and passed in. *)
  let links = ref [] and args = ref [] and buffers = ref [] and argv = ref [] in
  let argv_origin = ref None in
  List.iter
    (fun (e : entry) ->
      match e.key with
      | "name" -> set_scalar name e
      | "program" -> set_scalar program e
      | "entry" -> set_scalar entry_name e
      | "skip-init" -> set_scalar skip_init e
      | "link" -> links := Ll_file (resolve_file ~origin:e.origin e.value) :: !links
      | "harness" ->
          links := Inline {file = e.origin.file; line = e.value_line; text = e.value} :: !links
      | "arg" -> args := (e.value, e.origin) :: !args
      | "buffer" ->
          (* `buffer in: T = init` and `buffer: in : T = init` are the same
             request; [Entry.parse_buffer] reads the latter. *)
          let text =
            match e.arg with
            | Some name -> Printf.sprintf "%s : %s" name e.value
            | None -> e.value
          in
          buffers := (text, e.origin) :: !buffers
      | "argv" ->
          if Option.is_none !argv_origin then argv_origin := Some e.origin ;
          argv := List.rev_append (Str.split (Str.regexp "[ \t]+") e.value) !argv
      | key ->
          (* [check_key] accepted it, so this is a key the reader knows and the
             builder forgot. *)
          fail e.origin "the key %S is not handled (this is a bug in %s)" key __FILE__ )
    entries ;
  let args = List.rev !args and buffers = List.rev !buffers in
  let program =
    match !program with
    | Some (value, origin) -> resolve_file ~origin value
    | None -> failwith (Printf.sprintf "%s: no 'program:' line, so there is nothing to run" path)
  in
  let label =
    match !name with Some (value, _) -> value | None -> Filename.basename program
  in
  ( match (!entry_name, !argv_origin) with
  | Some (_, entry_origin), Some argv_origin ->
      fail argv_origin
        "'argv:' starts the program at @main, but 'entry:' at %s starts it elsewhere; \
         drop one of the two"
        (where entry_origin)
  | _ -> () ) ;
  let run =
    match !entry_name with
    | Some (entry, origin) ->
        let written (text, origin) = Entry.{text; origin = where origin} in
        From_entry
          Entry.
            { name = entry
            ; origin = where origin
            ; (* Several [arg:] lines are one argument list: the LLVM grammar does
                 the splitting, which is also why a single line may hold a whole
                 comma-separated list, commas nested in an aggregate and all. *)
              args =
                ( match args with
                | [] -> None
                | args ->
                    Some
                      { text = String.concat ", " (List.map fst args)
                      ; origin = origin_of_lines args } )
            ; buffers = List.map written buffers }
    | None ->
        List.iter
          (fun (key, requests) ->
            match requests with
            | (_, origin) :: _ ->
                fail origin "'%s:' needs an 'entry:' to give it to ('argv:' is what @main takes)"
                  key
            | [] -> () )
          [("arg", args); ("buffer", buffers)] ;
        ( match List.rev !argv with
        | [] -> Default_argv
        | words -> Argv words )
  in
  let skip_init =
    match !skip_init with
    | None -> false
    | Some (value, origin) -> boolean origin "skip-init" value
  in
  {label; program; links = List.rev !links; run; skip_init}

let load (path : string) : t = build ~path (read_entries ~stack:[] ~depth:0 path)

(** A run target as named on the command line: a manifest, or a bare [.ll] file,
    which means the manifest [program: <that file>] and nothing else. *)
let load_target (path : string) : t =
  if Filename.check_suffix path extension then load path
  else
    { label = Filename.basename path
    ; program = path
    ; links = []
    ; run = Default_argv
    ; skip_init = false }

let is_manifest (path : string) = Filename.check_suffix path extension

(** Parse one [link:] or [harness:] into the AST to link. Inline text is given the
    manifest's own file and line, so the parser's locations point at the harness
    as it is written rather than at line 1 of a nameless buffer. *)
let ast_of_source = function
  | Ll_file path -> IO.parse_file path
  | Inline {file; line; text} ->
      let lexbuf = Lexing.from_string text in
      IO.reset_lexbuf file line lexbuf ;
      ( try Llvm_lexer.parse lexbuf
        with e ->
          failwith
            (Printf.sprintf "%s:%d: this inlined LLVM does not parse (%s)" file line
               (Printexc.to_string e)) )
