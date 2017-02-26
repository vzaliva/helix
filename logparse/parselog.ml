open Batteries
open String
open Str
open Printf

let debug_regexp = regexp "^Debug: ?\\([0-9]+\\(\\.[0-9]+\\)*\\) ?: *"

let verbose = ref false
let debug = ref false
let ifname = ref ""
let ofname = ref ""

exception MissingArg of string

type kind =
  | Goal
  | Looking
  | SimpleApply of bool
  | SimpleEapply of bool
  | External of bool
  | NoMatch
  | Exact of bool
  | Unknown

let ok_fail_of_bool = function
  | true -> "[OK]"
  | false -> "[Fail]"

let string_of_kind = function
  | Looking        -> "Looking"
  | SimpleApply x  -> ok_fail_of_bool x ^ "SimpleApply"
  | SimpleEapply x -> ok_fail_of_bool x ^ "SimpleEapply"
  | External x     -> ok_fail_of_bool x ^ "External"
  | NoMatch        -> "NoMatch"
  | Exact x        -> ok_fail_of_bool x ^ "Exact"
  | Goal           -> "Goal"
  | Unknown        -> "???"

let is_err = function
  | Looking | NoMatch | Goal | Unknown -> false
  | SimpleApply x | SimpleEapply x | External x | Exact x  -> not x

let classifiers = [
    (regexp "^looking for", Looking) ;
    (regexp "^simple apply .* failed with", SimpleApply false) ;
    (regexp "^simple apply", SimpleApply true) ;
    (regexp "^simple eapply .* failed with", SimpleEapply false) ;
    (regexp "^simple eapply", SimpleEapply true) ;
    (regexp "^(\\*external\\*) .* failed with", External false) ;
    (regexp "^(\\*external\\*)", External true) ;
    (regexp "^no match for", NoMatch) ;
    (regexp "^(", Goal) ;
    (regexp "^exact .* failed with", Exact false) ;
    (regexp "^exact ", Exact true) ;
  ]

let classify l =
  let rec loop = function
    | [] -> Unknown
    | (r,c)::rs -> if string_match r l 0 then c else loop rs
  in
  loop classifiers

(* Seqence type and functions *)

type seq = int list

let string_of_seq = BatString.join "." %
                      BatList.map string_of_int

let seq_of_string = BatList.map int_of_string %
                      BatString.split_on_char '.'

let rec ( =@ ) a b =
  match a, b with
  | (x::xs), (y::ys) -> x=y && xs=@ys
  | [], [] -> true
  | [], (_::_) -> false
  | (_::_), [] -> false

(* True if 'h' starts with 'n', but not exactly the same *)
let rec ( >@ ) h n =
  match h, n with
  | (h::hs), (n::ns) -> n=h && hs >@ ns
  | [], [] -> false
  | [], (_::_) -> false
  | (_::_), [] -> true

(* Stack of states for DFS *)
type entry = {
    line: int;
    b: seq;
    kind: kind;
    msg: string
  }

let string_of_entry e =
  sprintf "%d:%s:%s:[%s]" e.line (string_of_seq e.b) (string_of_kind e.kind)
          (if !verbose then e.msg else "TODO")

let stack:(entry Stack.t) = Stack.create ()

let gen_entry l n =
  if string_match debug_regexp l 0 then
    let bs = matched_group 1 l in
    let me = match_end () in
    let m = string_after l me in
    let k = classify m in
    Some { line = n;
           b = seq_of_string bs;
           kind = k;
           msg = string_of_kind k ; (* TODO *)
         }
  else
    None

(* TODO: add styles *)
let dot_style_of_kind k =
  let col c = "[color=" ^ c ^ "]" in
  let sha s = "[shape=" ^ s ^ "]" in
  let errc c x = col (if x then c else "red") in
  match k with
  | Looking        -> sha "parallelogram" ^ col "black"
  | SimpleApply x  -> sha "ellipse" ^ errc "blue" x
  | SimpleEapply x -> sha "ellipse" ^ errc "blue" x
  | External x     -> sha "ellipse" ^ errc "pink" x
  | NoMatch        -> sha "trapezium" ^ col "red"
  | Exact x        -> sha "polygon" ^ errc "green" x
  | Goal           -> sha "box" ^ col "yellow"
  | Unknown        -> sha "point" ^ col "red"

let dot_of_entry {line; b; kind; msg} =
  let bs = string_of_seq b in
  sprintf "L%d %s [label=\"%s\\n%s\"]" line
          (dot_style_of_kind kind)
          msg bs

let rec dump_dot oc msibling prev =
  let link a mb = match mb with
    | Some b -> fprintf oc "\tL%d -> L%d;\n" a.line b.line;
    | None -> ()
  in
  if not (Stack.is_empty stack) then
    let p = Stack.top stack in
    if
      (match msibling with
       | Some sibling ->  sibling.b >@ p.b
       | None -> false)
    then
      (* we are at common parent. just link from it *)
      link p prev
    else
      begin
        let x = Stack.pop stack in
        (* if !debug then printf "\t\tPOP %s\n" (string_of_entry x); *)
        fprintf oc "\t%s;\n" (dot_of_entry x);
        link x prev;
        dump_dot oc msibling (Some p)
      end

let process_line oc l n =
  match gen_entry l n with
  | Some e ->
     printf "%s\n" (string_of_entry e);
     (* Pop/process pending entries (if any) *)
     dump_dot oc (Some e) None;
     (* now push new entry *)
     Stack.push e stack;
     if !debug then printf "\t\tPUSH: %s, stack size %d\n" (string_of_seq e.b) (Stack.length stack)
  | None ->
     if !debug && !verbose then printf "Not numbered: %d: %s\n" n l

let process_file ifilename ofilename =
  let ic = open_in ifilename in
  let oc = open_out ofilename in
  let rec loop m start current =
    let s = input_line ic in
    if not (is_empty m) && starts_with s "Debug" then
      begin
        process_line oc m start ; loop s current (current+1)
      end
    else
      loop (m ^ s) start (current+1)
  in
  try
    fprintf oc "digraph {\n" ;
    fprintf oc "\trankdir=\"LR\";\n" ;
    loop "" 1 1
  with End_of_file ->
    begin
      (* TODO: dump remaining stack *)
      dump_dot oc None None ;
      fprintf oc "}\n" ;
      close_in ic ;
      close_out oc
    end

let main =
  begin
    let speclist = [("-v", Arg.Set verbose, "Enables verbose mode");
                    ("-d", Arg.Set debug, "Enables debug mode");
                    ("-f", Arg.Set_string ifname, "File to process");
                    ("-o", Arg.Set_string ofname, "Output file");
                   ]
    in let usage_msg = "Parse log file. Options available:"
       in Arg.parse speclist print_endline usage_msg;
          if is_empty !ifname then raise (MissingArg "Must specify -f") ;
          if is_empty !ofname then raise (MissingArg "Must specify -o") ;
          process_file !ifname !ofname
  end

let () = main
