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

%token DECL CHAIN ASSIGN LOOP FUNC NTH CRETURN
%token <string> IDENTIFIER
%token EOF

%start <Ast.iprogram> i_program

%%

(* At top level we only allow function definitions. Chained or standalone *)
i_program:
    | f=i_function EOF { Program [f] }
    | CHAIN LPAREN fs=separated_nonempty_list(COMMA, i_function) RPAREN EOF {Program fs}
    ;

i_function:
    | FUNC LPAREN t=IDENTIFIER COMMA n=STRING COMMA LBRACKET a=separated_list(COMMA, i_var) RBRACKET COMMA b=i_stmt RPAREN {Function (n,Some t,a,b)}
    ;

i_var:
   | i=IDENTIFIER { Var (i,None) } (* will be extended by type annotatoins later *)
   ;

i_rvalue:
  | n=IDENTIFIER LPAREN a=separated_list(COMMA, i_rvalue) RPAREN {FunCall (n,a)}
  | v=i_var {VarRValue v}
  | f=FLOAT {FConst f}
  | i=INT {IConst i}
  | NTH LPAREN a=i_rvalue COMMA i=i_rvalue RPAREN { NthRvalue (a,i) }
  ;

i_lvalue:
  | v=i_var {VarLValue v}
  | NTH LPAREN a=i_lvalue COMMA i=i_rvalue RPAREN { NthLvalue (a,i) }
  ;

i_stmt:
  | DECL LPAREN LBRACKET a=separated_list(COMMA, i_var) RBRACKET COMMA b=i_stmt RPAREN {Decl (a,b)}
  | CHAIN LPAREN c=separated_nonempty_list(COMMA, i_stmt) RPAREN {Chain c}
  | ASSIGN LPAREN n=i_lvalue COMMA e=i_rvalue RPAREN {Assign (n,e)}
  | CRETURN LPAREN i=i_rvalue RPAREN { Return i }
  | LOOP LPAREN v=i_var COMMA LBRACKET f=INT TWODOT t=INT RBRACKET COMMA b=i_stmt RPAREN
    {Loop (v,f,t,b)}
  ;

