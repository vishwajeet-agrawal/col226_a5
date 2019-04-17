{
  open A3
  exception Not_implemented
  exception Syntax_Error
}

(*
  Below is a dummy implementation. Please note the following
  - Tokens are defined in A3.mly
  - Return type is token and not token list
  - End of buffer is indicated by EOF token below
  - There is no trailer. The scanner function is written in the wrapper file (test_a3.ml)
*)
rule read = parse
   eof                { EOF }
   | ['0'-'9']+ as n  { INT (int_of_string n) }
   | 'T'|"TRUE"|"true"|"True"           {BOOL (true)}
   | 'F'|"False"|"false"|"FALSE"              {BOOL (false)}
   | "ABS"|"abs"|"Abs"             {ABS}
   | '~'                    {TILDA}
   | "NOT"|"not"|"Not"     {NOT}
   | '+'     {PLUS}
   | '-'    {MINUS}
   | '*'    {TIMES}
   | '/'     {DIV}
   | "mod"|"MOD"|"Mod"    {REM}
   | "/\\"   {CONJ}
   | "\\/"   {DISJ}
   | "="     {EQ}
   | "let" |"LET" {LET}
   | "IN" |"in" {IN}
   | "end" | "END" {END}
   | "def" | "DEF" {DEF}
   | "||" {PARALLEL}
   | '\\' {BACKSLASH}
   | '.' {DOT}
   | "local" | "LOCAL" {LOCAL}
   | ">"     {GT}
   | '<'     {LT}
   | '('     {LP}
   | ')'     {RP}
   | "IF"|"if"     {IF}
   | ":"    {COLON}
   | "Tint" {TINT}
   | "Tbool" {TBOOL}
   | "->" {ARROW}
   | "THEN"|"then"   {THEN}
   | "ELSE"|"else"  {ELSE}
   | "FI"|"fi"     {FI}
   | ','  {COMMA}
   | "PROJ"|"Proj"|"proj"  {PROJ}
   | ';'  {SEMICOLON}
   | ['a'-'z' 'A'-'Z']+['a'-'z' 'A'-'Z' '0'-'9' '\'' '_']* as str {ID (str )}
   | ['\t' ' ' '\n'] {read lexbuf}
   | _                { raise Syntax_Error }
