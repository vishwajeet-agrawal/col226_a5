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

open Parsing;;
let _ = parse_error;;
# 2 "a3.mly"
    open A1
# 42 "a3.ml"
let yytransl_const = [|
  260 (* ABS *);
  261 (* TILDA *);
  262 (* NOT *);
  263 (* PLUS *);
  264 (* MINUS *);
  265 (* TIMES *);
  266 (* DIV *);
  267 (* REM *);
  268 (* CONJ *);
  269 (* DISJ *);
  270 (* EQ *);
  271 (* GT *);
  272 (* LT *);
  273 (* LP *);
  274 (* RP *);
  275 (* IF *);
  276 (* THEN *);
  277 (* ELSE *);
  278 (* FI *);
  279 (* COMMA *);
  280 (* PROJ *);
  281 (* LET *);
  282 (* IN *);
  283 (* END *);
  284 (* BACKSLASH *);
  285 (* DOT *);
  286 (* DEF *);
  287 (* SEMICOLON *);
  288 (* PARALLEL *);
  289 (* LOCAL *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* BOOL *);
  259 (* ID *);
    0|]

let yylhs = "\255\255\
\002\000\001\000\003\000\003\000\003\000\003\000\003\000\005\000\
\005\000\009\000\009\000\010\000\010\000\010\000\010\000\010\000\
\010\000\011\000\011\000\011\000\012\000\012\000\012\000\012\000\
\013\000\013\000\013\000\014\000\014\000\015\000\015\000\016\000\
\016\000\017\000\017\000\019\000\018\000\018\000\020\000\020\000\
\020\000\006\000\007\000\008\000\004\000\004\000\004\000\021\000\
\022\000\024\000\024\000\024\000\025\000\025\000\025\000\023\000\
\023\000\023\000\000\000\000\000"

let yylen = "\002\000\
\002\000\002\000\003\000\001\000\001\000\001\000\001\000\003\000\
\001\000\002\000\001\000\004\000\004\000\003\000\003\000\003\000\
\001\000\003\000\003\000\001\000\003\000\003\000\003\000\001\000\
\002\000\002\000\001\000\007\000\001\000\007\000\001\000\002\000\
\001\000\003\000\003\000\002\000\001\000\003\000\001\000\001\000\
\001\000\002\000\004\000\005\000\001\000\001\000\001\000\002\000\
\002\000\003\000\002\000\002\000\003\000\002\000\002\000\004\000\
\005\000\003\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\059\000\000\000\
\000\000\000\000\000\000\000\000\000\000\041\000\040\000\039\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\060\000\000\000\000\000\005\000\006\000\007\000\009\000\000\000\
\000\000\000\000\024\000\027\000\029\000\031\000\033\000\037\000\
\000\000\000\000\000\000\002\000\055\000\052\000\051\000\054\000\
\000\000\000\000\025\000\026\000\010\000\000\000\032\000\000\000\
\000\000\000\000\000\000\000\000\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\058\000\
\000\000\000\000\050\000\053\000\038\000\000\000\000\000\000\000\
\000\000\000\000\000\000\008\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\023\000\022\000\021\000\000\000\000\000\
\000\000\035\000\034\000\000\000\000\000\000\000\000\000\000\000\
\000\000\057\000\036\000\000\000\000\000\044\000\000\000\000\000\
\028\000\030\000"

let yydgoto = "\003\000\
\007\000\025\000\062\000\008\000\027\000\028\000\029\000\030\000\
\031\000\032\000\033\000\034\000\035\000\036\000\037\000\038\000\
\055\000\039\000\099\000\040\000\009\000\010\000\011\000\012\000\
\013\000"

let yysindex = "\066\000\
\004\255\225\255\000\000\004\255\001\255\004\255\000\000\017\000\
\247\254\014\255\050\255\004\255\004\255\000\000\000\000\000\000\
\008\002\008\002\228\001\225\255\225\255\030\255\004\255\069\255\
\000\000\200\001\066\255\000\000\000\000\000\000\000\000\013\255\
\062\255\043\255\000\000\000\000\000\000\000\000\000\000\000\000\
\065\255\078\255\067\255\000\000\000\000\000\000\000\000\000\000\
\063\255\072\255\000\000\000\000\000\000\007\255\000\000\083\255\
\094\255\073\255\076\255\228\001\000\000\195\255\228\001\008\002\
\234\001\002\002\008\002\008\002\008\002\008\002\008\002\000\000\
\225\255\004\255\000\000\000\000\000\000\225\255\225\255\075\255\
\225\255\225\255\066\255\000\000\062\255\008\002\062\255\008\002\
\062\255\043\255\043\255\000\000\000\000\000\000\195\255\074\255\
\038\255\000\000\000\000\111\255\108\255\139\255\195\255\062\255\
\062\255\000\000\000\000\225\255\092\255\000\000\167\255\047\255\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\012\001\031\001\063\001\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\074\001\000\000\000\000\000\000\000\000\042\001\
\097\000\001\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\138\001\168\001\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\126\001\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\106\001\000\000\129\000\000\000\161\000\000\000\
\193\000\033\000\065\000\000\000\000\000\000\000\136\001\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\158\001\225\000\
\001\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\254\255\255\255\058\000\000\000\000\000\000\000\
\239\255\000\000\206\255\007\000\245\255\000\000\000\000\008\000\
\041\000\000\000\000\000\000\000\000\000\000\000\078\000\000\000\
\000\000"

let yytablesize = 800
let yytable = "\026\000\
\020\000\053\000\041\000\042\000\043\000\051\000\052\000\014\000\
\015\000\016\000\017\000\018\000\019\000\085\000\087\000\089\000\
\044\000\054\000\056\000\060\000\004\000\058\000\045\000\020\000\
\077\000\021\000\064\000\065\000\066\000\078\000\022\000\023\000\
\019\000\005\000\024\000\104\000\006\000\105\000\014\000\015\000\
\016\000\017\000\018\000\019\000\046\000\084\000\057\000\014\000\
\015\000\016\000\060\000\069\000\070\000\071\000\020\000\107\000\
\021\000\092\000\093\000\094\000\078\000\022\000\023\000\020\000\
\018\000\024\000\001\000\002\000\067\000\068\000\095\000\059\000\
\096\000\090\000\091\000\097\000\100\000\063\000\102\000\103\000\
\047\000\048\000\072\000\014\000\015\000\016\000\017\000\018\000\
\019\000\049\000\050\000\073\000\074\000\075\000\080\000\060\000\
\017\000\101\000\081\000\020\000\106\000\021\000\079\000\076\000\
\082\000\111\000\022\000\023\000\109\000\112\000\024\000\014\000\
\015\000\016\000\017\000\018\000\019\000\083\000\098\000\114\000\
\000\000\000\000\000\000\060\000\000\000\000\000\000\000\020\000\
\016\000\021\000\000\000\108\000\000\000\000\000\022\000\023\000\
\000\000\000\000\024\000\014\000\015\000\016\000\017\000\018\000\
\019\000\000\000\000\000\000\000\000\000\000\000\000\000\060\000\
\000\000\000\000\000\000\020\000\000\000\021\000\000\000\000\000\
\014\000\000\000\022\000\023\000\000\000\110\000\024\000\014\000\
\015\000\016\000\017\000\018\000\019\000\000\000\000\000\000\000\
\000\000\000\000\000\000\060\000\000\000\000\000\000\000\020\000\
\000\000\021\000\000\000\000\000\113\000\000\000\022\000\023\000\
\015\000\000\000\024\000\014\000\015\000\016\000\017\000\018\000\
\019\000\000\000\000\000\000\000\000\000\000\000\000\000\060\000\
\000\000\000\000\000\000\020\000\000\000\021\000\000\000\000\000\
\000\000\000\000\022\000\023\000\000\000\000\000\024\000\000\000\
\013\000\014\000\015\000\016\000\017\000\018\000\019\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\020\000\000\000\021\000\000\000\000\000\000\000\000\000\
\022\000\023\000\000\000\000\000\024\000\000\000\000\000\000\000\
\012\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
\020\000\000\000\000\000\045\000\020\000\020\000\020\000\020\000\
\020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
\020\000\020\000\020\000\020\000\020\000\000\000\046\000\020\000\
\020\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
\019\000\011\000\000\000\000\000\019\000\019\000\019\000\019\000\
\019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
\019\000\019\000\019\000\019\000\019\000\000\000\047\000\019\000\
\019\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
\018\000\004\000\000\000\000\000\018\000\018\000\018\000\018\000\
\018\000\018\000\018\000\018\000\018\000\018\000\018\000\018\000\
\018\000\018\000\018\000\018\000\018\000\000\000\000\000\018\000\
\018\000\017\000\017\000\017\000\017\000\017\000\017\000\000\000\
\000\000\003\000\000\000\000\000\017\000\017\000\017\000\017\000\
\017\000\017\000\017\000\017\000\017\000\017\000\017\000\017\000\
\017\000\017\000\017\000\017\000\017\000\042\000\000\000\017\000\
\017\000\016\000\016\000\016\000\016\000\016\000\016\000\056\000\
\000\000\048\000\000\000\000\000\016\000\016\000\016\000\016\000\
\016\000\016\000\016\000\016\000\016\000\016\000\016\000\016\000\
\016\000\016\000\016\000\016\000\016\000\043\000\000\000\016\000\
\016\000\014\000\014\000\014\000\014\000\014\000\014\000\049\000\
\000\000\000\000\000\000\000\000\014\000\014\000\014\000\014\000\
\014\000\014\000\014\000\014\000\014\000\014\000\014\000\014\000\
\014\000\014\000\014\000\014\000\014\000\000\000\000\000\014\000\
\014\000\015\000\015\000\015\000\015\000\015\000\015\000\061\000\
\000\000\000\000\000\000\000\000\015\000\015\000\015\000\015\000\
\015\000\015\000\015\000\015\000\015\000\015\000\015\000\015\000\
\015\000\015\000\015\000\015\000\015\000\000\000\000\000\015\000\
\015\000\013\000\013\000\013\000\013\000\013\000\013\000\000\000\
\000\000\000\000\000\000\000\000\013\000\013\000\013\000\013\000\
\013\000\013\000\013\000\013\000\013\000\013\000\013\000\013\000\
\013\000\013\000\013\000\013\000\013\000\000\000\000\000\013\000\
\013\000\012\000\012\000\012\000\012\000\012\000\012\000\000\000\
\000\000\000\000\000\000\000\000\012\000\012\000\012\000\012\000\
\012\000\012\000\012\000\012\000\012\000\012\000\012\000\012\000\
\012\000\012\000\012\000\012\000\012\000\045\000\000\000\012\000\
\012\000\000\000\000\000\000\000\000\000\045\000\045\000\000\000\
\000\000\000\000\011\000\011\000\011\000\011\000\011\000\011\000\
\046\000\000\000\000\000\000\000\000\000\011\000\011\000\000\000\
\046\000\046\000\011\000\011\000\011\000\011\000\011\000\011\000\
\011\000\011\000\011\000\011\000\011\000\011\000\000\000\000\000\
\011\000\011\000\004\000\004\000\004\000\004\000\004\000\004\000\
\047\000\000\000\000\000\000\000\000\000\000\000\004\000\000\000\
\047\000\047\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\004\000\004\000\004\000\004\000\000\000\000\000\
\004\000\004\000\003\000\003\000\003\000\003\000\003\000\003\000\
\000\000\000\000\000\000\000\000\000\000\000\000\003\000\000\000\
\000\000\000\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\000\000\000\000\
\003\000\003\000\000\000\000\000\000\000\000\000\000\000\042\000\
\000\000\042\000\042\000\042\000\042\000\000\000\000\000\042\000\
\042\000\056\000\000\000\048\000\042\000\042\000\000\000\000\000\
\000\000\056\000\056\000\048\000\048\000\000\000\056\000\056\000\
\000\000\048\000\000\000\000\000\000\000\000\000\000\000\043\000\
\000\000\043\000\043\000\043\000\043\000\000\000\000\000\043\000\
\043\000\049\000\000\000\000\000\043\000\043\000\000\000\000\000\
\000\000\049\000\049\000\000\000\000\000\000\000\049\000\000\000\
\014\000\015\000\016\000\017\000\018\000\019\000\000\000\000\000\
\000\000\000\000\000\000\000\000\060\000\000\000\000\000\000\000\
\020\000\000\000\021\000\000\000\000\000\000\000\000\000\022\000\
\023\000\000\000\000\000\024\000\014\000\015\000\016\000\017\000\
\018\000\019\000\014\000\015\000\016\000\017\000\018\000\000\000\
\000\000\000\000\000\000\000\000\020\000\000\000\021\000\086\000\
\000\000\000\000\020\000\022\000\021\000\000\000\000\000\000\000\
\000\000\022\000\014\000\015\000\016\000\017\000\018\000\000\000\
\014\000\015\000\016\000\017\000\018\000\000\000\000\000\088\000\
\000\000\000\000\020\000\000\000\021\000\000\000\000\000\000\000\
\020\000\022\000\021\000\000\000\000\000\000\000\000\000\022\000"

let yycheck = "\002\000\
\000\000\019\000\004\000\003\001\006\000\017\000\018\000\001\001\
\002\001\003\001\004\001\005\001\006\001\064\000\065\000\066\000\
\000\000\020\000\021\000\013\001\017\001\023\000\032\001\017\001\
\018\001\019\001\014\001\015\001\016\001\023\001\024\001\025\001\
\000\000\030\001\028\001\086\000\033\001\088\000\001\001\002\001\
\003\001\004\001\005\001\006\001\031\001\063\000\017\001\001\001\
\002\001\003\001\013\001\009\001\010\001\011\001\017\001\018\001\
\019\001\069\000\070\000\071\000\023\001\024\001\025\001\017\001\
\000\000\028\001\001\000\002\000\007\001\008\001\073\000\003\001\
\074\000\067\000\068\000\078\000\079\000\012\001\081\000\082\000\
\031\001\032\001\018\001\001\001\002\001\003\001\004\001\005\001\
\006\001\012\000\013\000\014\001\026\001\031\001\001\001\013\001\
\000\000\023\001\026\001\017\001\027\001\019\001\020\001\032\001\
\029\001\108\000\024\001\025\001\001\001\018\001\028\001\001\001\
\002\001\003\001\004\001\005\001\006\001\060\000\078\000\112\000\
\255\255\255\255\255\255\013\001\255\255\255\255\255\255\017\001\
\000\000\019\001\255\255\021\001\255\255\255\255\024\001\025\001\
\255\255\255\255\028\001\001\001\002\001\003\001\004\001\005\001\
\006\001\255\255\255\255\255\255\255\255\255\255\255\255\013\001\
\255\255\255\255\255\255\017\001\255\255\019\001\255\255\255\255\
\000\000\255\255\024\001\025\001\255\255\027\001\028\001\001\001\
\002\001\003\001\004\001\005\001\006\001\255\255\255\255\255\255\
\255\255\255\255\255\255\013\001\255\255\255\255\255\255\017\001\
\255\255\019\001\255\255\255\255\022\001\255\255\024\001\025\001\
\000\000\255\255\028\001\001\001\002\001\003\001\004\001\005\001\
\006\001\255\255\255\255\255\255\255\255\255\255\255\255\013\001\
\255\255\255\255\255\255\017\001\255\255\019\001\255\255\255\255\
\255\255\255\255\024\001\025\001\255\255\255\255\028\001\255\255\
\000\000\001\001\002\001\003\001\004\001\005\001\006\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\017\001\255\255\019\001\255\255\255\255\255\255\255\255\
\024\001\025\001\255\255\255\255\028\001\255\255\255\255\255\255\
\000\000\001\001\002\001\003\001\004\001\005\001\006\001\007\001\
\008\001\255\255\255\255\000\000\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\255\255\000\000\031\001\
\032\001\001\001\002\001\003\001\004\001\005\001\006\001\007\001\
\008\001\000\000\255\255\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\255\255\000\000\031\001\
\032\001\001\001\002\001\003\001\004\001\005\001\006\001\007\001\
\008\001\000\000\255\255\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\255\255\255\255\031\001\
\032\001\001\001\002\001\003\001\004\001\005\001\006\001\255\255\
\255\255\000\000\255\255\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\000\000\255\255\031\001\
\032\001\001\001\002\001\003\001\004\001\005\001\006\001\000\000\
\255\255\000\000\255\255\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\000\000\255\255\031\001\
\032\001\001\001\002\001\003\001\004\001\005\001\006\001\000\000\
\255\255\255\255\255\255\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\255\255\255\255\031\001\
\032\001\001\001\002\001\003\001\004\001\005\001\006\001\000\000\
\255\255\255\255\255\255\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\255\255\255\255\031\001\
\032\001\001\001\002\001\003\001\004\001\005\001\006\001\255\255\
\255\255\255\255\255\255\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\255\255\255\255\031\001\
\032\001\001\001\002\001\003\001\004\001\005\001\006\001\255\255\
\255\255\255\255\255\255\255\255\012\001\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\028\001\018\001\255\255\031\001\
\032\001\255\255\255\255\255\255\255\255\026\001\027\001\255\255\
\255\255\255\255\001\001\002\001\003\001\004\001\005\001\006\001\
\018\001\255\255\255\255\255\255\255\255\012\001\013\001\255\255\
\026\001\027\001\017\001\018\001\019\001\020\001\021\001\022\001\
\023\001\024\001\025\001\026\001\027\001\028\001\255\255\255\255\
\031\001\032\001\001\001\002\001\003\001\004\001\005\001\006\001\
\018\001\255\255\255\255\255\255\255\255\255\255\013\001\255\255\
\026\001\027\001\017\001\018\001\019\001\020\001\021\001\022\001\
\023\001\024\001\025\001\026\001\027\001\028\001\255\255\255\255\
\031\001\032\001\001\001\002\001\003\001\004\001\005\001\006\001\
\255\255\255\255\255\255\255\255\255\255\255\255\013\001\255\255\
\255\255\255\255\017\001\018\001\019\001\020\001\021\001\022\001\
\023\001\024\001\025\001\026\001\027\001\028\001\255\255\255\255\
\031\001\032\001\255\255\255\255\255\255\255\255\255\255\018\001\
\255\255\020\001\021\001\022\001\023\001\255\255\255\255\026\001\
\027\001\018\001\255\255\018\001\031\001\032\001\255\255\255\255\
\255\255\026\001\027\001\026\001\027\001\255\255\031\001\032\001\
\255\255\032\001\255\255\255\255\255\255\255\255\255\255\018\001\
\255\255\020\001\021\001\022\001\023\001\255\255\255\255\026\001\
\027\001\018\001\255\255\255\255\031\001\032\001\255\255\255\255\
\255\255\026\001\027\001\255\255\255\255\255\255\031\001\255\255\
\001\001\002\001\003\001\004\001\005\001\006\001\255\255\255\255\
\255\255\255\255\255\255\255\255\013\001\255\255\255\255\255\255\
\017\001\255\255\019\001\255\255\255\255\255\255\255\255\024\001\
\025\001\255\255\255\255\028\001\001\001\002\001\003\001\004\001\
\005\001\006\001\001\001\002\001\003\001\004\001\005\001\255\255\
\255\255\255\255\255\255\255\255\017\001\255\255\019\001\014\001\
\255\255\255\255\017\001\024\001\019\001\255\255\255\255\255\255\
\255\255\024\001\001\001\002\001\003\001\004\001\005\001\255\255\
\001\001\002\001\003\001\004\001\005\001\255\255\255\255\014\001\
\255\255\255\255\017\001\255\255\019\001\255\255\255\255\255\255\
\017\001\024\001\019\001\255\255\255\255\255\255\255\255\024\001"

let yynames_const = "\
  ABS\000\
  TILDA\000\
  NOT\000\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  REM\000\
  CONJ\000\
  DISJ\000\
  EQ\000\
  GT\000\
  LT\000\
  LP\000\
  RP\000\
  IF\000\
  THEN\000\
  ELSE\000\
  FI\000\
  COMMA\000\
  PROJ\000\
  LET\000\
  IN\000\
  END\000\
  BACKSLASH\000\
  DOT\000\
  DEF\000\
  SEMICOLON\000\
  PARALLEL\000\
  LOCAL\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  BOOL\000\
  ID\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 28 "a3.mly"
                 (_1)
# 418 "a3.ml"
               : A1.exptree))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'definition) in
    Obj.repr(
# 31 "a3.mly"
                 (_1)
# 425 "a3.ml"
               : A1.definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'conj_expression) in
    Obj.repr(
# 34 "a3.mly"
                                  (Disjunction (_1,_3))
# 433 "a3.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'conj_expression) in
    Obj.repr(
# 35 "a3.mly"
                    (_1)
# 440 "a3.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'call) in
    Obj.repr(
# 36 "a3.mly"
         (_1)
# 447 "a3.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'lambda) in
    Obj.repr(
# 37 "a3.mly"
           (_1)
# 454 "a3.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'let_exp) in
    Obj.repr(
# 38 "a3.mly"
            (_1)
# 461 "a3.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'conj_expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'not) in
    Obj.repr(
# 41 "a3.mly"
                           (Conjunction (_1,_3))
# 469 "a3.ml"
               : 'conj_expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'not) in
    Obj.repr(
# 42 "a3.mly"
        (_1)
# 476 "a3.ml"
               : 'conj_expression))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'not) in
    Obj.repr(
# 45 "a3.mly"
          (Not(_2))
# 483 "a3.ml"
               : 'not))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'compare) in
    Obj.repr(
# 46 "a3.mly"
           (_1)
# 490 "a3.ml"
               : 'not))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'compare) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'addsub) in
    Obj.repr(
# 49 "a3.mly"
                       (LessTE(_1,_4))
# 498 "a3.ml"
               : 'compare))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'compare) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'addsub) in
    Obj.repr(
# 50 "a3.mly"
                        (GreaterTE(_1,_4))
# 506 "a3.ml"
               : 'compare))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'compare) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'addsub) in
    Obj.repr(
# 51 "a3.mly"
                     (GreaterT(_1,_3))
# 514 "a3.ml"
               : 'compare))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'compare) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'addsub) in
    Obj.repr(
# 52 "a3.mly"
                     (LessT(_1,_3))
# 522 "a3.ml"
               : 'compare))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'compare) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'addsub) in
    Obj.repr(
# 53 "a3.mly"
                     (Equals(_1,_3))
# 530 "a3.ml"
               : 'compare))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'addsub) in
    Obj.repr(
# 54 "a3.mly"
          (_1)
# 537 "a3.ml"
               : 'compare))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'addsub) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'divmultrem) in
    Obj.repr(
# 57 "a3.mly"
                          (Sub (_1,_3))
# 545 "a3.ml"
               : 'addsub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'addsub) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'divmultrem) in
    Obj.repr(
# 58 "a3.mly"
                          (Add(_1,_3))
# 553 "a3.ml"
               : 'addsub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'divmultrem) in
    Obj.repr(
# 59 "a3.mly"
              (_1)
# 560 "a3.ml"
               : 'addsub))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'divmultrem) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'absolute) in
    Obj.repr(
# 62 "a3.mly"
                          (Rem(_1,_3))
# 568 "a3.ml"
               : 'divmultrem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'divmultrem) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'absolute) in
    Obj.repr(
# 63 "a3.mly"
                           (Div(_1,_3))
# 576 "a3.ml"
               : 'divmultrem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'divmultrem) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'absolute) in
    Obj.repr(
# 64 "a3.mly"
                             (Mult(_1,_3))
# 584 "a3.ml"
               : 'divmultrem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'absolute) in
    Obj.repr(
# 65 "a3.mly"
            (_1)
# 591 "a3.ml"
               : 'divmultrem))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'absolute) in
    Obj.repr(
# 68 "a3.mly"
               (Abs(_2))
# 598 "a3.ml"
               : 'absolute))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'absolute) in
    Obj.repr(
# 69 "a3.mly"
                  (Negative (_2))
# 605 "a3.ml"
               : 'absolute))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ifte) in
    Obj.repr(
# 70 "a3.mly"
         (_1)
# 612 "a3.ml"
               : 'absolute))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'expression) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'expression) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 73 "a3.mly"
                                                  (IfThenElse(_2,_4,_6))
# 621 "a3.ml"
               : 'ifte))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'project) in
    Obj.repr(
# 74 "a3.mly"
          (_1)
# 628 "a3.ml"
               : 'ifte))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : int) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'tuple) in
    Obj.repr(
# 77 "a3.mly"
                                     (Project ((_3,_5),_7))
# 637 "a3.ml"
               : 'project))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'tuple) in
    Obj.repr(
# 78 "a3.mly"
          (_1)
# 644 "a3.ml"
               : 'project))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'tuple1) in
    Obj.repr(
# 81 "a3.mly"
            (Tuple (List.length _2,_2))
# 651 "a3.ml"
               : 'tuple))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'paren) in
    Obj.repr(
# 82 "a3.mly"
         (_1)
# 658 "a3.ml"
               : 'tuple))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tuple0) in
    Obj.repr(
# 85 "a3.mly"
                          (_1::_3)
# 666 "a3.ml"
               : 'tuple1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'tuple1) in
    Obj.repr(
# 86 "a3.mly"
                           (_1::_3)
# 674 "a3.ml"
               : 'tuple1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 89 "a3.mly"
                ([_1])
# 681 "a3.ml"
               : 'tuple0))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'constant) in
    Obj.repr(
# 92 "a3.mly"
           (_1)
# 688 "a3.ml"
               : 'paren))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 93 "a3.mly"
                    (InParen (_2))
# 695 "a3.ml"
               : 'paren))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 96 "a3.mly"
     (Var (_1))
# 702 "a3.ml"
               : 'constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : bool) in
    Obj.repr(
# 97 "a3.mly"
        (B (_1))
# 709 "a3.ml"
               : 'constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 98 "a3.mly"
       (N (_1))
# 716 "a3.ml"
               : 'constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 101 "a3.mly"
                        (FunctionCall(_1,_2))
# 724 "a3.ml"
               : 'call))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 104 "a3.mly"
                              (FunctionAbstraction(_2,_4))
# 732 "a3.ml"
               : 'lambda))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'definition) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expression) in
    Obj.repr(
# 107 "a3.mly"
                                   (Let(_2,_4))
# 740 "a3.ml"
               : 'let_exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'seq_definition) in
    Obj.repr(
# 111 "a3.mly"
                   (_1)
# 747 "a3.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'par_definition) in
    Obj.repr(
# 112 "a3.mly"
                   (_1)
# 754 "a3.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sim_definition) in
    Obj.repr(
# 113 "a3.mly"
                    (_1)
# 761 "a3.ml"
               : 'definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'seqi_definition) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'sim_definition) in
    Obj.repr(
# 116 "a3.mly"
                                 (Sequence(_1 @ [_2]))
# 769 "a3.ml"
               : 'seq_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'pari_definition) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'sim_definition) in
    Obj.repr(
# 119 "a3.mly"
                                 (Parallel(_1 @ [_2]))
# 777 "a3.ml"
               : 'par_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'seqi_definition) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'sim_definition) in
    Obj.repr(
# 122 "a3.mly"
                                             (_1 @ [_2])
# 785 "a3.ml"
               : 'seqi_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'sim_definition) in
    Obj.repr(
# 123 "a3.mly"
                             ([_1])
# 792 "a3.ml"
               : 'seqi_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'par_definition) in
    Obj.repr(
# 124 "a3.mly"
                             ([_1])
# 799 "a3.ml"
               : 'seqi_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'pari_definition) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'sim_definition) in
    Obj.repr(
# 127 "a3.mly"
                                             (_1 @ [_2])
# 807 "a3.ml"
               : 'pari_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'sim_definition) in
    Obj.repr(
# 128 "a3.mly"
                            ([_1])
# 814 "a3.ml"
               : 'pari_definition))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'seq_definition) in
    Obj.repr(
# 129 "a3.mly"
                            ([_1])
# 821 "a3.ml"
               : 'pari_definition))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 132 "a3.mly"
                         (Simple(_2,_4))
# 829 "a3.ml"
               : 'sim_definition))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'definition) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'definition) in
    Obj.repr(
# 133 "a3.mly"
                                      (Local (_2,_4))
# 837 "a3.ml"
               : 'sim_definition))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'definition) in
    Obj.repr(
# 134 "a3.mly"
                    (_2)
# 844 "a3.ml"
               : 'sim_definition))
(* Entry def_parser *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry exp_parser *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let def_parser (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : A1.definition)
let exp_parser (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : A1.exptree)