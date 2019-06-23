%{
  open Tree;;
%}
%token <string> VAR
%token IMPL AND OR NOT
%token OPEN CLOSE
%token EOF
%right IMPL
%left OR
%left AND
%nonassoc NOT
%start main
%type <Tree.tree> main
%%
main:
        expr EOF           { $1 }
expr:
        | VAR               { Var ($1) }
        | OPEN expr CLOSE   { $2 }
        | NOT expr          { Neg ($2) }
        | expr IMPL expr    { Impl ($1, $3) }
        | expr AND expr     { Conj ($1, $3) }
        | expr OR expr      { Disj ($1, $3) }
