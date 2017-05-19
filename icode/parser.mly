%{
    open Ast
%}

%token <float> FLOAT
%token <int> INT

%token COMMA
%token TWODOT
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token <string> STRING

%token DECL CHAIN ASSIGN LOOP FUNC CRETURN
%token <string> IDENTIFIER
%token EOF

%start <Ast.iprogram> i_program

%%

i_program:
    | f=i_function* EOF { Program f }
    ;

i_function:
    | FUNC LPAREN t=IDENTIFIER COMMA n=STRING COMMA LBRACKET a=separated_list(i_var,COMMA) RBRACKET COMMA b=i_stmt RPAREN {Function (n,t,a,b)}
    ;

i_var:
   | i=IDENTIFIER { Var (i,None) } (* will be extended by type annotatoins later *)
   ;

i_stmt:
  | DECL LPAREN LBRACKET a=separated_list(i_var,COMMA) LBRACKET COMMA b=i_stmt RPAREN {Decl (a,b)}
  | CHAIN LPAREN c=separated_nonempty_list(i_stmt, COMMA) RPAREN {Chain c}
  | ASSIGN LPAREN n=i_var COMMA e=i_expr RPAREN {Assign (n,e)}
  | CRETURN LPAREN i=i_expr RPAREN { Return i }
  ;

i_expr:
  | n=IDENTIFIER LPAREN a=separated_list(i_expr, COMMA) RPAREN {FunCall (n,a)}
  | f=FLOAT {FConst f}
  | i=INT {IConst i}
  | LOOP LPAREN v=IDENTIFIER LBRACKET f=INT TWODOT t=INT RBRACKET RPAREN {Loop (v,f,t)}
  ;
