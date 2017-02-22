open Std
open Str
open BatList
open BatFile
open BatIO

open Dirtools

(* TODO: match mutliline import statements *)
let import_regexp = Str.regexp "^[ \t]*Require[ \t]+Import[ \t]+\\(\\([A-Za-z_\\.]+\\)\\([ \t]+[A-Za-z_\\.]+\\)*\\)\\."

let verbose = ref false
let replace = ref false
let debug = ref false
let wrap = ref false

let nilstrlst:(string list) = []
let coqargs = ref nilstrlst
let coqcmd = ref "coqc"


(** Exception to report unknown argument *)
exception BadArg of string

(** Parse command line, set options flags, and return pair containing list of coq options and list of .v files to be processed *)
let parse_cmd_line () =
  let args = Array.to_list Sys.argv in
  let fname_regexp = regexp "[A-Za-z_][A-Za-z_']+\\.v" in (* TODO: unicode *)
  let (files, justargs) = partition (fun x -> string_match fname_regexp x 0) args in
  let (cmiargs, newargs) = partition (fun x -> BatString.starts_with x "-cmi-") justargs in
  let flags = [("-cmi-verbose", verbose) ; ("-cmi-replace", replace) ; ("-cmi-debug", debug) ; ("-cmi-wrap", wrap) ] in
  let options = [("-cmi-coqc", coqcmd)] in
  ignore (map (fun n ->
              try
                if BatString.contains n '=' then
                  let (on,ov) = BatString.split n "=" in
                  assoc on options := ov
                else
                  assoc n flags := true
              with
                Not_found -> raise (BadArg n)
            ) cmiargs);
  (newargs, files)

(** Run Coq compiler on given file and return exit code. 'quiet' flag supresses compiler output *)
let compile name quiet =
  let cmd = (!coqcmd) ^ " " ^ (String.concat " " !coqargs) ^ " " ^ name ^
              (if quiet then " > /dev/null 2>&1" else "") in
  if !debug then Printf.printf "Executing: %s\n" cmd;
  BatSys.command cmd

(** Try to compile given coq program and return exit code. *)
let try_compile s =
  let d = make_tmp_dir 0o755 ~prefix:"coq_min_imports" ~suffix:".tmpdir" in
  let (out, name) = open_temporary_out ~mode:[`create] ~suffix:".v" ~temp_dir:d () in
  write_line out s;
  close_out out;
  let res = compile name true in
  rmrf d ;
  (res == 0)

let gen_import lst =
  (if is_empty lst then "" else
     "Require Import " ^ (String.concat " " lst) ^ ".\n")

let rec process_require pre post lst res =
  match lst with
  | [] -> res
  | x::xs ->
     let nl = ((rev xs)@res) in
     let body = pre ^ (gen_import nl) ^ post in
     if !debug then Printf.printf "\n==================\n %s \n==================\n" body;
     process_require pre post xs
                     (if try_compile body then
                        (if !verbose then Printf.printf "\t-%s\n" x;
                         res)
                      else
                        (if !verbose then Printf.printf "\t+%s\n" x;
                         (cons x res))
                     )

let rec process_imports s p saved =
  if p<0 then
    (s,saved)
  else
    try
      let x = search_backward import_regexp s p in
      let is = (matched_group 1 s) in
      let me = match_end () in
      let il = Str.split (regexp "[ \t]+") is in
      let pre = (string_before s x) in
      let post = (string_after s me) in
      let il' = process_require pre post (rev il) [] in
      let saved' = length il - length il' in
      let s' = if saved > 0 then s else pre ^ gen_import il' ^ post in
      process_imports s' (x-1) (saved+saved')
    with
      Not_found -> (s, saved)

let process_file fname =
  if !verbose then Printf.printf "Processing %s\n" fname;
  let s = input_file fname in
  let (s',saved) = process_imports s (String.length s) 0 in
  if saved>0 then
    let dumpf fn txt =
      let out = open_out ~mode:[`create ; `trunc] fn in
      write_line out txt;
      close_out out in
    if !replace then
      let backup_fname = fname ^ ".bak" in
      (if !verbose then Printf.printf "Removing %d imports from %s (saving %s)\n" saved fname backup_fname) ; Sys.rename fname backup_fname ; dumpf fname s'
    else
      let new_fname = fname ^ ".new" in
      (if !verbose then Printf.printf "Writing modified copy of %s as %s with %d imports removed\n" fname new_fname saved) ; dumpf new_fname s'
  else
    (if !verbose then Printf.printf "Nothing to remove in %s\n" fname)
  ; saved

let () =
  try
    let (args,files) = parse_cmd_line () in
    if is_empty files then
      (Printf.printf "Usage: coq_min_imports <coq_flags> [-cmi-verbose] [-cmi-replace] [-cmi-wrap] [-cmi-coqc=cmd]  <files...>\n" ; exit 1)
    else
      (coqargs := tl args;
       let saved = fold_left (+) 0 (map process_file files) in
       if !verbose then Printf.printf "Removed %d imports from %d files\n" saved (length files);
       if !wrap then exit (compile (String.concat " " files) false)
      )
  with
    BadArg n -> Printf.printf "Unknown argument %s\n" n; exit 1
