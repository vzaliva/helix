%{
    open Ast
%}

%token <float> FLOAT
%token <int> INT
%token <string> STRING

%token COMMA
%token TWODOT
%token LPAREN RPAREN
%token LBRACKET RBRACKET

%token DECL CHAIN ASSIGN LOOP FUNC NTH CRETURN EOF
%token <string> IDENTIFIER

%start <Ast.iprogram> i_program

%%

i_program:
    | f=i_stmt EOF { Program [f] }
    | CHAIN LPAREN fs=separated_nonempty_list(COMMA, i_stmt) RPAREN EOF {Program fs}
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
  | FUNC LPAREN t=IDENTIFIER COMMA n=STRING COMMA LBRACKET a=separated_list(COMMA, i_var) RBRACKET COMMA b=i_stmt RPAREN {Function (n,Some t,a,b)}
  | DECL LPAREN LBRACKET a=separated_list(COMMA, i_var) RBRACKET COMMA b=i_stmt RPAREN {Decl (a,b)}
  | CHAIN LPAREN c=separated_nonempty_list(COMMA, i_stmt) RPAREN {Chain c}
  | ASSIGN LPAREN n=i_lvalue COMMA e=i_rvalue RPAREN {Assign (n,e)}
  | CRETURN LPAREN i=i_rvalue RPAREN { Return i }
  | LOOP LPAREN v=i_var COMMA LBRACKET f=i_rvalue TWODOT t=i_rvalue RBRACKET COMMA b=i_stmt RPAREN
    {Loop (v,f,t,b)}
  ;

