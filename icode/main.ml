open Typechecker
open Format

let filename = Sys.argv.(1)

let () =
    let inBuffer = open_in filename in
    let lineBuffer = Lexing.from_channel inBuffer in
    try
      let ast = Parser.i_program Lexer.main lineBuffer in
      let ast = fix_operator_types ast in
      let types = Typechecker.collect_vars ast in
      pp_print_list ~pp_sep:pp_print_newline Ast.pr_ivar std_formatter types
    with
        | Typechecker.Error msg -> Printf.fprintf stderr "Type check failed: %s%!\n" msg
        | Lexer.Error msg -> Printf.fprintf stderr "Lexer error %s%!\n" msg
        | Parser.Error -> Printf.fprintf stderr "Parsing error at offset %d: syntax error.\n%!" (Lexing.lexeme_start lineBuffer)
