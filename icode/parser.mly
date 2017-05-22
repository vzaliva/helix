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

%token DECL CHAIN DATA ASSIGN LOOP FUNC NTH SKIP IF CRETURN EOF
%token TVOID TINT TREAL TBOOL

%token <string> IDENTIFIER

%start <Ast.istmt> i_program

%%

i_program:
    | f=i_stmt EOF { Chain [f] }
    | EOF { Chain [] }
    ;

i_var:
   | i=IDENTIFIER { Var (i,UnknownType) } (* will be extended by type annotatoins later *)
   ;

i_rvalue:
  | n=IDENTIFIER LPAREN a=separated_list(COMMA, i_rvalue) RPAREN {FunCall (n,a)}
  | v=IDENTIFIER {VarRValue v}
  | f=FLOAT {FConst f}
  | i=INT {IConst i}
  | NTH LPAREN a=i_rvalue COMMA i=i_rvalue RPAREN { NthRvalue (a,i) }
  ;

i_lvalue:
  | v=IDENTIFIER {VarLValue v}
  | NTH LPAREN a=i_lvalue COMMA i=i_rvalue RPAREN { NthLvalue (a,i) }
  ;

i_type:
  | TINT   {IntType}
  | TREAL  {RealType}
  | TBOOL  {BoolType}
  | TVOID  {VoidType}
  | n=IDENTIFIER {OtherType n}
  ;

i_stmt:
  | SKIP {Skip}
  | FUNC LPAREN t=i_type COMMA n=STRING COMMA LBRACKET a=separated_list(COMMA, i_var) RBRACKET COMMA b=i_stmt RPAREN {Function (n,t,a,b)}
  | DECL LPAREN LBRACKET a=separated_list(COMMA, i_var) RBRACKET COMMA b=i_stmt RPAREN {Decl (a,b)}
  | CHAIN LPAREN c=separated_list(COMMA, i_stmt) RPAREN {Chain c}
  | DATA n=i_var COMMA v=separated_list(COMMA, i_rvalue) COMMA b=i_stmt LPAREN RPAREN {Data (n,v,b)}
  | ASSIGN LPAREN n=i_lvalue COMMA e=i_rvalue RPAREN {Assign (n,e)}
  | CRETURN LPAREN i=i_rvalue RPAREN { Return i }
  | IF LPAREN v=i_rvalue COMMA t=i_stmt COMMA e=i_stmt RPAREN { If (v,t,e) }
  | LOOP LPAREN v=i_var COMMA LBRACKET f=i_rvalue TWODOT t=i_rvalue RBRACKET COMMA b=i_stmt RPAREN  { Loop (v,f,t,b) }
  ;
