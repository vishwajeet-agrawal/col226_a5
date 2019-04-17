#directory "_build";; (* Consider this folder when looking for files *)
#load "a0.cmo";;
#load "a1.cmo";;
#load "a2.cmo";;
#load "a3.cmo";;
#load "a4.cmo";;
#load "a5.cmo";;
open A0;;
open A1;;
open A2;;
open A3;;
open A4;;
open A5;;

closure_table:=[];;
closure_type_table:=[];;
environment:=[];;
environment_type:=[];;

add_closure_type "Fact" "Tint -> Tint";;
add_closure_type "Fib" "Tint -> Tint";;
add_closure_type "Sum" "Tint -> Tint";;

let c1 = make_recursive_closure "Fact" "\\n:Tint.if n<0 then 0 else if n = 0 then 1 else n*(Fact (n-1)) fi fi" false;;
let c2 = make_recursive_closure "Fib" "\\n:Tint.if n=0 then 0 else if n=1 then 1 else (Fib (n-1))+(Fib (n-2)) fi fi" false;;
let c3 = make_recursive_closure "Sum" "\\n:Tint.if n=0 then 0 else n + (Sum (n-1)) fi" false;;
add_recursive_closure "Fact" c1;;
add_recursive_closure "Fib" c2;;
add_recursive_closure "Sum" c3;;


let a1 = execute_krivine "Fact 20";;
let a2 = execute_krivine "Fact 10";;
let a3 = execute_krivine "Fact 1";;
let a4 = execute_krivine "Fib 10";;
let a5 = execute_krivine "Fib 15";;
let a6 = execute_krivine "Sum 10";;
let a7 = execute_krivine "Sum 14";;
let a8 = execute_krivine "Sum 100";;

let c1 = make_closure "\\b:Tbool.if b then Fact else Fib fi" true;;
add_closure "FibOrFact" c1;;
add_closure "Absolute" (make_closure "\\m:Tint. if m<0 then ~m else m fi" false);;
execute_krivine "(FibOrFact T) 20";;
execute_krivine "(FibOrFact F) 15";;
let c2 = Clos(exp_parser "(FibOrFact T) 25",!(closure_table));;
let a9 = krivine_machine c2 [];;

let int1 = Num (mk_big 433);;
let b1 = Bool(true);;
let e1 = exp_parser "\\n:Tint.if n<0 then 0 else if n = 0 then 1 else n*(Fact (n-1)) fi fi"
let rec vcl1 = VClos(compile e1,[("Fact",vcl1)]);;
(* let vcl2 = *)
add_answer "Fact" "Tint -> Tint" vcl1;;

add_answer "X" "Tint" (execute_secd "34");;
add_answer "Y" "Tbool" (execute_secd "T");;
add_answer "Z" "Tint->Tint" (execute_secd "\\n:Tint .if X>30 then n*X-n else X*n fi");;
execute_secd "Z";;
execute_secd "Z 2";;
execute_krivine "Absolute";;
add_closure "X" (make_closure "4" false);;
execute_krivine "Absolute ~X";;