open Std
open Str
open BatList
open BatFile
open BatIO
open String

(* TODO: match mutliline import statements *)
let import_regexp = Str.regexp "^[ \t]*Require[ \t]+Import[ \t]+\\(\\([A-Za-z_\\.]+\\)\\([ \t]+[A-Za-z_\\.]+\\)*\\)\\."

let verbose = ref false
let debug = ref false
let fname = ref ""

let process_file fname =
  print_endline ("File: " ^ fname)

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
