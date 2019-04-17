open A4
open A3
open A2
open A1

exception Not_implemented
exception Type_error

let closure_table = ref[]
let closure_type_table = ref[]
let environment = ref[]
let environment_type = ref[]

let type_parser s = A3.type_parser A2.read (Lexing.from_string s)
let exp_parser s = A3.exp_parser A2.read (Lexing.from_string s)

let make_closure s b = let e1 = exp_parser s in
  if hastype (!closure_type_table) e1 Tunit then 
  if b then (Clos(e1,!(closure_table)))
  else (Clos(e1,[]))
  else raise Type_error

let make_recursive_closure s se b =
  let e1 = exp_parser se in
  if hastype (!closure_type_table) e1 Tunit then 
  if b then
  let rec cl1  = 
  (Clos(e1,(s,cl1)::(!(closure_table)))) in cl1
  else let rec cl1  = 
  (Clos(e1,[(s,cl1)])) in cl1
  else raise Type_error

(* let exp_to_clos e = (e,!(closure_table))
let exp_to_clos_notable e = (e,[]) *)



let execute_secd e = let e1 = exp_parser e in
if hastype (!environment_type) e1 Tunit then
secd_machine [] (!environment) (compile (e1)) []
else raise Type_error

let execute_krivine e = let e1 = exp_parser e in
  if hastype (!closure_type_table) e1 Tunit then
  krivine_machine (Clos(e1,!(closure_table))) []
  else raise Type_error

let add_closure s c = 
     (closure_table:=(s,c)::(!(closure_table))); 
    let e = match c with Clos(e1,cl) -> e1 in
    closure_type_table:=(s,infertype (!closure_type_table) e)::(!closure_type_table)

let add_closure_type s t =
  let t1 = type_parser t in 
  closure_type_table:=(s,t1)::(!closure_type_table)

let add_answer s t a = 
  let t1 = type_parser t in
    environment:=(s,a)::(!environment);
    environment_type:=(s,t1)::(!environment_type)

let add_answer_type s t =
  let t1 = type_parser t in
  environment_type:=(s,t1)::(!environment_type)

let add_recursive_closure s c = 
  (closure_table:=(s,c)::(!(closure_table)))
(* 
let execute_krivine1 cl = 
  krivine_machine_in cl [] *)
(* 
let get_rec_clos s t c = 
  add_closure_type s t; add_recursive_closure s c *)