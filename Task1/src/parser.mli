type token =
  | VAR of (string)
  | IMPL
  | AND
  | OR
  | NOT
  | OPEN
  | CLOSE
  | EOF
  | COMMA
  | PROOF

val body :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.tree_t
val header :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Tree.tree_t list
