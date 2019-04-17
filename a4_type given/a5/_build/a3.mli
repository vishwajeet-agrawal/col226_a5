type token =
  | INT of (int)
  | BOOL of (bool)
  | ID of (string)
  | ABS
  | TILDA
  | NOT
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | REM
  | CONJ
  | DISJ
  | EQ
  | GT
  | LT
  | LP
  | RP
  | IF
  | THEN
  | ELSE
  | FI
  | COMMA
  | PROJ
  | LET
  | IN
  | END
  | BACKSLASH
  | DOT
  | DEF
  | SEMICOLON
  | PARALLEL
  | LOCAL
  | EOF
  | COLON
  | TBOOL
  | TINT
  | ARROW

val def_parser :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> A1.definition
val exp_parser :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> A1.exptree
val type_parser :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> A1.exptype
