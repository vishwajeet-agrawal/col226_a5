#directory "_build";; (* Consider this folder when looking for files *)
#load "a0.cmo";;
#load "a1.cmo";;
#load "a2.cmo";;
#load "a3.cmo";;
#load "a4.cmo";;
open A0;;
open A1;;
open A2;;
open A3;;
open A4;;

exception Not_implemented
(* Helper function to print *)
let rec print_tree tr = match tr with
  N a -> "INT " ^ (string_of_int a)
  | _ -> raise Not_implemented
;;
let rec print_answer tr = match tr with
  Num a -> print_num a
  | Bool a -> string_of_bool a
  | _ -> raise Not_implemented
;;
let rec print_value tr = match tr with
  NumVal a -> string_of_int a
  | BoolVal a -> string_of_bool a
  | _ -> raise Not_implemented
;;
let rec print_def df = match df with
  Simple((l,t),r) -> "def " ^ l ^ " = " ^ (print_tree r)
  | _ -> raise Not_implemented
;;

let rho s = match s with
  "X" -> NumVal 5
  |  "Y" -> BoolVal true
  |  "Z" -> TupVal (3, [NumVal 5; BoolVal true; NumVal 1])
  | _ -> raise Not_implemented

(* Input is given as value and output is an answer *)
let rec toAnswer v = match v with
  NumVal a     -> Num (mk_big a)
| BoolVal b    -> Bool b
| TupVal (n,xs) -> Tup (n, List.map toAnswer xs)
| FunVal (s,e) -> Fun (s,toAnswer e)
| Vclosure (e,vcl) -> let rec toans vcl = match vcl with [] -> [] 
| (s,vc1)::vcll -> (s,toAnswer vc1)::(toans vcll) in VClos (compile e,toans vcl);;
(* Input is given as string and output is an answer *)
let binding rho s = toAnswer (rho s);;

(* Both use the same lexer in A1 but different parser in A3 *)
let exp_parser s = A3.exp_parser A2.read (Lexing.from_string s) ;;
let def_parser s = A3.def_parser A2.read (Lexing.from_string s) ;;

(* Input is given as string and output is a value *)


(* Sample parsing *)
print_endline ( print_tree (exp_parser "5" ));;
print_endline ( print_def (def_parser "def a:Tint=5" ));;

(* Sample test case *)
let e = (exp_parser "\\X:Tint.Y" );;
let t = Tfunc (Tint, Tbool);;

(* Type assumptions as a list of tuples of the form (variable name, type) *)
let g = [("X", Tint); ("Y", Tbool); ("Z", Ttuple([Tint ; Tbool ; Tint])) ;("W", Tfunc (Tint, Tbool))];;
let d = def_parser "def U:Tint = X ; def V:Tbool = Y" ;;
let g_dash = [("U", Tint); ("V", Tbool)];;
let env = [("X",Num (mk_big 10));("Y", Bool (true));("Z", Fun ( "X",VClos([VAR("X")],[])))];;
assert(hastype g e t);;
assert(yields g d g_dash);;
let e = exp_parser "Fact 20"
let efib = exp_parser "Fib 10"
let rec factclos =  Clos(exp_parser "\\n:Tint.if n=0 then 1 else n * (Fact (n-1)) fi",[("Fact",factclos)])
let rec fibonacci = Clos(exp_parser "\\n:Tint.if n=0 then 0 else if n = 1 then 1 else (Fib (n-1)) + (Fib (n-2)) fi fi",[("Fib",fibonacci)])
let rec fiborfact = Clos(exp_parser "\\b:Tbool.if b then Fact else Fib fi",[("Fact",factclos);("Fib",fibonacci)])
let cl1 = Clos(e,["Fact",factclos])
let cl2 = Clos(efib,["Fib",fibonacci])
let cl3 = Clos(e,[("FibOrFact",fiborfact)])
let print_ans ans =
let rec print_answer ans = match
ans with 
|Num (bg) -> print_bytes (print_num bg)
|Bool (b) -> print_bytes (string_of_bool (b))
|Tup (n,tp) -> (match tp with [] ->print_string("") ; 
                  |tpx::tpxs -> print_answer tpx; print_string " "; print_answer (Tup((n-1),tpxs));)
| _ -> raise Not_implemented in print_answer ans; print_endline("");
;;
(* returns eval *)
let krivine_eval cl = krivine_machine cl ([])
(* returns answer *)

let execute ex = secd_machine [] env (compile ex) [] 

let make_rec_clos s