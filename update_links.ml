(* update_links.ml -- recompute the line numbers of the links to Rocq
   declarations in markdown or yaml files.

   A link names its declaration in its title:

     [Lemma 0](./prelim.v#L525-L528 "error_exactMul")

   For each such link, the program looks in prelim.v for the line that
   starts with "Lemma error_exactMul" (or Theorem, Definition, ...), and
   puts in the link the lines from there to the end of the statement (the
   first "." followed by a blank, outside comments and strings).  Links
   without a title are left as they are.

   Usage:  ocaml update_links.ml [-check] FILE...
     rewrites each FILE in place (meta.yml, README.md);
     -check: rewrites nothing, exits with 1 if a link is out of date.
   Exits with 2, rewriting nothing, if a name is not found or found twice. *)

let keywords =
  [ "Theorem"; "Lemma"; "Corollary"; "Fact"; "Remark"; "Proposition";
    "Definition"; "Fixpoint"; "CoFixpoint"; "Inductive"; "Let";
    "Notation" ]

let read_file f =
  let ic = open_in_bin f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

let write_file f s =
  let oc = open_out_bin f in
  output_string oc s; close_out oc

let is_ident c =
  match c with
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
  | _ -> false

let is_blank c = c = ' ' || c = '\n' || c = '\t' || c = '\r'

(* the lines of a file, as (offset of the line start) array *)
let line_starts s =
  let l = ref [0] in
  String.iteri (fun i c -> if c = '\n' then l := (i + 1) :: !l) s;
  Array.of_list (List.rev !l)

(* the line number (from 1) of offset i *)
let line_of starts i =
  let rec go lo hi = (* largest k with starts.(k) <= i *)
    if lo >= hi then lo
    else let m = (lo + hi + 1) / 2 in
      if starts.(m) <= i then go m hi else go lo (m - 1) in
  go 0 (Array.length starts - 1) + 1

(* the offset of the "." ending the sentence that starts at i: the first
   "." followed by a blank or the end, outside (nested) comments and
   strings *)
let sentence_end s i =
  let n = String.length s in
  let rec go i depth instr =
    if i >= n then None
    else if instr then
      (if s.[i] = '"' then go (i + 1) depth false else go (i + 1) depth true)
    else if i + 1 < n && s.[i] = '(' && s.[i + 1] = '*' then
      go (i + 2) (depth + 1) false
    else if depth > 0 && i + 1 < n && s.[i] = '*' && s.[i + 1] = ')' then
      go (i + 2) (depth - 1) false
    else if depth > 0 then go (i + 1) depth false
    else if s.[i] = '"' then go (i + 1) depth true
    else if s.[i] = '.' && (i + 1 = n || is_blank s.[i + 1]) then Some i
    else go (i + 1) depth false in
  go i 0 false

(* the declarations of name in s: offsets of the lines "Keyword name ..." *)
let find_decls s starts name =
  let res = ref [] in
  Array.iter (fun st ->
    let n = String.length s in
    let i = ref st in
    while !i < n && (s.[!i] = ' ' || s.[!i] = '\t') do incr i done;
    List.iter (fun kw ->
      let k = String.length kw and m = String.length name in
      let j = !i + k in
      if j + 1 + m <= n && String.sub s !i k = kw && is_blank s.[j] then begin
        let j = ref j in
        while !j < n && (s.[!j] = ' ' || s.[!j] = '\t') do incr j done;
        if !j + m <= n && String.sub s !j m = name
           && (!j + m = n || not (is_ident s.[!j + m])) then
          res := !i :: !res
      end) keywords) starts;
  List.rev !res

let files = Hashtbl.create 17

let source dir f =
  let p = Filename.concat dir f in
  match Hashtbl.find_opt files p with
  | Some x -> x
  | None ->
    let s = read_file p in
    let x = (s, line_starts s) in
    Hashtbl.add files p x; x

exception Bad of string

(* the range "Ln-Lm" of name in file f *)
let range dir f name =
  let s, starts = (try source dir f
                   with Sys_error _ -> raise (Bad (f ^ ": cannot read"))) in
  match find_decls s starts name with
  | [] -> raise (Bad (Printf.sprintf "%s: no declaration of %s" f name))
  | _ :: _ :: _ ->
    raise (Bad (Printf.sprintf "%s: %s declared more than once" f name))
  | [i] ->
    match sentence_end s i with
    | None -> raise (Bad (Printf.sprintf "%s: %s has no end" f name))
    | Some e ->
      let a = line_of starts i and b = line_of starts e in
      if a = b then Printf.sprintf "L%d" a else Printf.sprintf "L%d-L%d" a b

(* rewrite the links "(./F.v#L... "name")" of text t; returns the new text
   and the number of links changed *)
let update dir t =
  let b = Buffer.create (String.length t) and changed = ref 0 in
  let n = String.length t in
  let rec go i =
    if i >= n then ()
    else if t.[i] = '(' && i + 2 < n && t.[i + 1] = '.' && t.[i + 2] = '/' then
      match String.index_from_opt t i ')' with
      | None -> Buffer.add_substring b t i (n - i)
      | Some close ->
        let link = String.sub t (i + 1) (close - i - 1) in
        (* link = ./F.v#RANGE "name" *)
        (match String.index_opt link '#', String.index_opt link '"' with
         | Some h, Some q when h < q && link.[String.length link - 1] = '"' ->
           let f = String.sub link 2 (h - 2) in
           let name = String.sub link (q + 1) (String.length link - q - 2) in
           let old = String.trim (String.sub link (h + 1) (q - h - 1)) in
           let r = range dir f name in
           if r <> old then incr changed;
           Buffer.add_string b
             (Printf.sprintf "(./%s#%s \"%s\")" f r name)
         | _ -> Buffer.add_string b ("(" ^ link ^ ")"));
        go (close + 1)
    else (Buffer.add_char b t.[i]; go (i + 1)) in
  go 0;
  Buffer.contents b, !changed

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let check, args =
    match args with "-check" :: a -> true, a | a -> false, a in
  if args = [] then (prerr_endline "usage: ocaml update_links.ml [-check] FILE..."; exit 2);
  let results =
    try List.map (fun f ->
        let dir = Filename.dirname f in
        let t = read_file f in
        let t', c = update dir t in
        (f, t, t', c)) args
    with Bad m -> prerr_endline ("update_links: " ^ m); exit 2 in
  let total = List.fold_left (fun a (_, _, _, c) -> a + c) 0 results in
  List.iter (fun (f, _, t', c) ->
    if c > 0 then begin
      Printf.printf "%s: %d link(s) %s\n" f c
        (if check then "out of date" else "updated");
      if not check then write_file f t'
    end) results;
  if total = 0 then print_endline "all links up to date";
  if check && total > 0 then exit 1
