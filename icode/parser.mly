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

%start <Ast.i_program list> source

%%

source:
    | EOF { [] }
