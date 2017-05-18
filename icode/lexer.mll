{
  open Parser

  exception Error of string
}

let lowercase = ['a'-'z' '\223'-'\246' '\248'-'\255' '_'] 
let uppercase = ['A'-'Z' '\192'-'\214' '\216'-'\222'] 
let identchar =
    ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']

rule token = parse
(* ignore whitespace *)
| [' ' '\t' '\n'] { token lexbuf }

(* numeric literals *)
| ['0'-'9']*'.'['0'-'9']+ as f
    { FLOAT (float_of_string f) }
| ['0'-'9']+ as i
    { INT (int_of_string i) }

(* special characters *)
| ','  { COMMA    }
| ".." { TWODOT   }
| '('  { LPAREN   }
| ')'  { RPAREN   }
| '['  { LBRACKET }
| ']'  { RBRACKET }

(* string literals *)
| '"'
     { let buffer = Buffer.create 10 in
         STRING (stringl buffer lexbuf)
     }   
 and  stringl buffer = parse
 | '"' { Buffer.contents buffer }
 | "\\t" { Buffer.add_char buffer '\t'; stringl buffer lexbuf }
 | "\\n" { Buffer.add_char buffer '\n'; stringl buffer lexbuf }
 | '\\' '"' { Buffer.add_char buffer '"'; stringl buffer lexbuf }
 | '\\' '\\' { Buffer.add_char buffer '\\'; stringl buffer lexbuf }
 | eof { raise End_of_file }
 | _ as char { Buffer.add_char buffer char; stringl buffer lexbuf }
 
(* some reserved words below *)    
| "decl"    { DECL    }
| "chain"   { CHAIN   }
| "assign"  { ASSIGN  }
| "loop"    { LOOP    }
| "func"    { FUNC    }
| "creturn" { CRETURN }

| ((lowercase | uppercase) (identchar+)) as i
    { IDENTIFIER as i }
    
| eof
    { EOF }
| _
    { raise (Error (Printf.sprintf "At offset %d: unexpected character.\n" (Lexing.lexeme_start lexbuf))) }