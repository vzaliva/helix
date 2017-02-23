open Std
open Str
open String

let debug_regexp = Str.regexp "^Debug: ?[0-9]+\\(\\.[0-9]+\\)* ?:"

let verbose = ref false
let debug = ref false
let fname = ref ""

let process_line l =
  if string_match debug_regexp l 0 then
    print_endline ("OK " ^ l)
  else
    print_endline ("ERR " ^ l)

let process_file filename =
  let chan = open_in filename in
  let rec loop m = 
    let s = input_line chan in
    let open BatString in
    if not (is_empty m) && starts_with s "Debug" then
      (process_line m ; loop s)
    else
      loop (m ^ s)
  in
  try
    loop ""
  with End_of_file ->
    close_in chan

let main =
  begin
  let speclist = [("-v", Arg.Set verbose, "Enables verbose mode");
                  ("-d", Arg.Set verbose, "Enables debug mode");
                  ("-f", Arg.Set_string fname, "File to process");
                 ]
  in let usage_msg = "Parse log file. Options available:"
     in Arg.parse speclist print_endline usage_msg;
        process_file !fname
  end

let () = main
