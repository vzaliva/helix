open Std
open Str
open String

let debug_regexp = Str.regexp "^Debug: ?\\([0-9]+\\(\\.[0-9]+\\)*\\) ?: *"

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
  | Looking      -> "Looking"
  | SimpleApply x  -> ok_fail_of_bool x ^ "SimpleApply"
  | SimpleEapply x -> ok_fail_of_bool x ^ "SimpleEapply"
  | External x     -> ok_fail_of_bool x ^ "External"
  | NoMatch      -> "NoMatch"
  | Exact x       -> ok_fail_of_bool x ^ "Exact"
  | Goal         -> "Goal"
  | Unknown      -> "???"

let classifiers = [
    (Str.regexp "^looking for", Looking) ;
    (Str.regexp "^simple apply .* failed with", SimpleApply false) ;
    (Str.regexp "^simple apply", SimpleApply true) ;
    (Str.regexp "^simple eapply .* failed with", SimpleEapply false) ;
    (Str.regexp "^simple eapply", SimpleEapply true) ;
    (Str.regexp "^(\\*external\\*) .* failed with", External false) ;
    (Str.regexp "^(\\*external\\*)", External true) ;
    (Str.regexp "^no match for", NoMatch) ;
    (Str.regexp "^(", Goal) ;
    (Str.regexp "^exact .* failed with", Exact false) ;
    (Str.regexp "^exact ", Exact true) ;
  ]

let classify l =
  let rec loop = function
    | [] -> Unknown
    | (r,c)::rs -> if string_match r l 0 then c else loop rs
  in
  loop classifiers

let process_line l n =
  if string_match debug_regexp l 0 then
    let b = matched_group 1 l in
    let me = match_end () in
    let m = string_after l me in
    let k = classify m in
    print_endline (string_of_int n ^ ":" ^ b ^ ":" ^ (string_of_kind k) ^ ":" ^ m)
  else
    if !debug && !verbose then print_endline ("Not numbered: " ^ string_of_int n ^ ":" ^ l)

let process_file ifilename ofilename =
  let ic = open_in ifilename in
  let oc = open_out ofilename in
  let rec loop m start current =
    let s = input_line ic in
    let open BatString in
    if not (is_empty m) && starts_with s "Debug" then
      begin
        process_line m start ; loop s current (current+1)
      end
    else
      loop (m ^ s) start (current+1)
  in
  try
    Printf.fprintf oc "graph {\n" ;
    loop "" 1 1
  with End_of_file ->
       begin
         Printf.fprintf oc "}\n" ;
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
        if BatString.is_empty !ifname then raise (MissingArg "Must specify -f") ;
        if BatString.is_empty !ofname then raise (MissingArg "Must specify -o") ;
        process_file !ifname !ofname
  end

let () = main
