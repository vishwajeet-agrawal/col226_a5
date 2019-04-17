%{
    open A1
%}

/*
- Tokens (token name and rules) are modified wrt to A2. Please make necessary changes in A3
- LP and RP are left and right parenthesis
- Write grammar rules to recognize
  - >= <= from GT EQ LT tokens
  - if then else fi
*/
/* Tokens are defined below.  */
%token <int> INT
%token <bool> BOOL
%token <string> ID
%token ABS TILDA NOT PLUS MINUS TIMES DIV REM CONJ DISJ EQ GT LT LP RP IF THEN ELSE FI COMMA PROJ 
LET IN END BACKSLASH DOT DEF SEMICOLON PARALLEL LOCAL EOF COLON TBOOL TINT TFUNC TTUPLE
%start def_parser exp_parser type_parser
%type <A1.definition> def_parser /* Returns definitions */
%type <A1.exptree> exp_parser /* Returns expression */
%type <A1.exptype> type_parser
%%
/*
DESIGN a grammar for a simple expression language, taking care to enforce precedence rules (e.g., BODMAS)
The language should contain the following types of expressions:  integers and booleans.
*/

exp_parser:
  expression EOF {$1}

def_parser:
  definition EOF {$1}

expression:
  expression DISJ conj_expression {Disjunction ($1,$3)}
  | conj_expression {$1}
  | call {$1}
  | lambda {$1}
  | let_exp {$1}

conj_expression: 
  conj_expression CONJ not {Conjunction ($1,$3)}
  | not {$1}

not:
  NOT not {Not($2)}
  |compare {$1}

compare:
  compare LT EQ addsub {LessTE($1,$4)}
  |compare GT EQ addsub {GreaterTE($1,$4)}
  |compare GT addsub {GreaterT($1,$3)}
  |compare LT addsub {LessT($1,$3)}
  |compare EQ addsub {Equals($1,$3)}
  |addsub {$1}

addsub:
  addsub MINUS divmultrem {Sub ($1,$3)}
  |addsub PLUS divmultrem {Add($1,$3)}
  |divmultrem {$1}

divmultrem:
  divmultrem REM absolute {Rem($1,$3)} 
  |divmultrem DIV absolute {Div($1,$3)}
  |divmultrem TIMES absolute {Mult($1,$3)}
  |absolute {$1}

absolute:
  ABS absolute {Abs($2)}
  |TILDA absolute {Negative ($2)}
  | ifte {$1}

ifte:
 IF expression THEN expression ELSE expression FI {IfThenElse($2,$4,$6)}
 |project {$1}

project:
  PROJ LP INT COMMA INT RP tuple     {Project (($3,$5),$7)}
  | tuple {$1}

tuple:
  LP tuple1 {Tuple (List.length $2,$2)}
  |paren {$1}

tuple1:
  expression COMMA tuple0 {$1::$3}
  |expression COMMA tuple1 {$1::$3}

tuple0:
  expression RP {[$1]}

paren:
  constant {$1}
  |LP expression RP {InParen ($2)}

constant:
  ID {Var ($1)}
  |BOOL {B ($1)}
  |INT {N ($1)}

call:
  lambda expression {FunctionCall($1,$2)}  

lambda:
  BACKSLASH ID DOT expression {FunctionAbstraction($2,$4)}

let_exp:
  LET definition IN expression END {Let($2,$4)} 


definition:
  | seq_definition {$1}
  | par_definition {$1}
  | sim_definition  {$1}
  
seq_definition:
  seqi_definition sim_definition {Sequence($1 @ [$2])}

par_definition:
  pari_definition sim_definition {Parallel($1 @ [$2])}

seqi_definition:
  | seqi_definition sim_definition SEMICOLON {$1 @ [$2]}
  | sim_definition SEMICOLON {[$1]}
  | par_definition SEMICOLON {[$1]}

pari_definition:
  | pari_definition sim_definition  PARALLEL {$1 @ [$2]}
  | sim_definition PARALLEL {[$1]}
  | seq_definition PARALLEL {[$1]}

sim_definition:
  |DEF ID COLON type EQ expression  {Simple($2,$6)}
  |LOCAL definition IN definition END {Local ($2,$4)}
  |LP definition RP {$2}

type:
  |TINT {Tint}
  |TBOOL {Tbool}
  |typel {Ttuple($2)}
  |TFUNC LP type COMMA type RP {Tfunc($1,$2)}

typel:
  |typel RP {$1}
typel_1:
  |LP type {[$2]}
  |type_1 COMMA type {$1 @ [$2]}
;