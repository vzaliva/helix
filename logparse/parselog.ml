open Std
open Str
open String

let debug_regexp = Str.regexp "^Debug: ?\\([0-9]+\\(\\.[0-9]+\\)*\\) ?: *"

let verbose = ref false
let debug = ref false
let fname = ref ""

exception UnparseableLine of (string*int)

let process_line l n =
  if string_match debug_regexp l 0 then
    let b = (matched_group 1 l) in
    let me = match_end () in
    let m = (string_after l me) in
    print_endline b
  else
    if !debug then print_endline (string_of_int n ^ ":" ^ l)
    else raise (UnparseableLine (l,n))

let process_file filename =
  let chan = open_in filename in
  let rec loop m start current = 
    let s = input_line chan in
    let open BatString in
    if not (is_empty m) && starts_with s "Debug" then
      begin
        process_line m start ; loop s current (current+1)
      end
    else
      loop (m ^ s) start (current+1)
  in
  try
    loop "" 1 1
  with End_of_file ->
    close_in chan

let main =
  begin
  let speclist = [("-v", Arg.Set verbose, "Enables verbose mode");
                  ("-d", Arg.Set debug, "Enables debug mode");
                  ("-f", Arg.Set_string fname, "File to process");
                 ]
  in let usage_msg = "Parse log file. Options available:"
     in Arg.parse speclist print_endline usage_msg;
        process_file !fname
  end

let () = main
