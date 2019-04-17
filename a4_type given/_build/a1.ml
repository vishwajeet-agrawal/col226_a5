(* Dummy implementation of A1 *)
(* *)
open A0
exception Not_implemented

type exptype = Tint | Tunit | Tbool | Ttuple of (exptype list) | Tfunc of (exptype * exptype) | Tvar of string 

(* abstract syntax *)
type  exptree =  
  Var of string (* variables starting with a Capital letter, represented as alphanumeric strings with underscores (_) and apostrophes (') *)
  | N of int      (* Integer constant *)
  | B of bool     (* Boolean constant *)
  (* unary operators on integers *)
  | Abs of exptree                   (* abs *)
  | Negative of exptree              (* unary minus ~ *)
  (* unary operators on booleans *)
  | Not of exptree
  (* binary operators on integers *)
  | Add of exptree * exptree         (* Addition + *)
  | Sub of exptree * exptree         (* Subtraction - *)
  | Mult of exptree * exptree        (* Multiplication * *)
  | Div of exptree * exptree         (* div *)
  | Rem of exptree * exptree         (* mod *)
  (* binary operators on booleans *)
  | Conjunction of exptree * exptree (* conjunction /\ *)
  | Disjunction of exptree * exptree (* binary operators on booleans \/ *)
  (* comparison operations on integers *)
  | Equals of exptree * exptree      (* = *)
  | GreaterTE of exptree * exptree   (* >= *)
  | LessTE of exptree * exptree      (* <= *)
  | GreaterT of exptree * exptree    (* > *)
  | LessT of exptree * exptree       (* < *)
  (* expressions using parenthesis *)
  | InParen of exptree               (* ( ) *)
  (* a conditional expression *)
  | IfThenElse of exptree * exptree * exptree (* if then else fi  *)
  (* creating n-tuples (n >= 0) *)
  | Tuple of int * (exptree list)
  (* projecting the i-th component of an expression (which evaluates to an n-tuple, and 1 <= i <= n) *)
  | Project of (int*int) * exptree   (* Proj((i,n), e)  0 < i <= n *)
  | Let of definition * exptree
  | FunctionAbstraction of (string * exptype) * exptree
  | FunctionCall of exptree * exptree

  and definition =
    Simple of (string * exptype) * exptree
  | Simple_untyped of (string * exptree)
  | Sequence of (definition list)
  | Parallel of (definition list)
  | Local of definition * definition
(* opcodes of the stack machine (in the same sequence as above) *)
type opcode = VAR of string | NCONST of bigint | BCONST of bool | ABS | UNARYMINUS | NOT
  | PLUS | MINUS | MULT | DIV | REM | CONJ | DISJ | EQS | GTE | LTE | GT | LT
  | PAREN | IFTE | TUPLE of int | PROJ of int*int | LET | FABS | FCALL
  | SIMPLEDEF | SEQCOMPOSE | PARCOMPOSE | LOCALDEF

(* The language should contain the following types of expressions:  integers and booleans *)
type answer = Num of bigint | Bool of bool | Tup of int * (answer list)
type value = NumVal of int | BoolVal of bool | TupVal of int * (value list)

exception InvalidExptree
let  intans ans = match ans with NumVal (x) -> x | _-> raise InvalidExptree
let getboolans ans = match ans with BoolVal (x) -> x | _ -> raise InvalidExptree
let rec eval ex rho = 
  
  match ex with 
    | Var (x) -> rho x
    | N ( x) -> NumVal ( x)
		| Sub (a,b) -> NumVal (( intans (eval a rho)) - ( intans (eval b rho)))
		| Add  (a,b) -> NumVal ( ( intans (eval a rho)) + ( intans (eval b rho)))
		| Rem   (a,b) -> NumVal ( ( intans (eval a rho)) mod ( intans (eval b rho)))
		| Div   (a,b) -> NumVal ( ( intans (eval a rho)) / ( intans (eval b rho)))
		| Mult  (a,b) -> NumVal ( ( intans (eval a rho)) * ( intans (eval b rho)))
		| Abs   a     -> let s = intans (eval a rho) in if (s <= 0) then NumVal (-s) else NumVal (s)
    | Negative   a     -> NumVal ( - ( intans (eval a rho)))
    | B ( x) -> BoolVal (x)
    | Not ( x) -> let ans = getboolans (eval x rho)  in  BoolVal (not ans)
    | Conjunction (x, y) -> let a1 = getboolans (eval x rho) in let a2 = getboolans (eval y rho) in 
                            BoolVal (a1 && a2)
    | Disjunction (x,y)  -> let a1 = getboolans (eval x rho) in let a2 = getboolans (eval y rho) in 
                            BoolVal (a1 || a2)
    | Equals (x,y) ->  let a1 = eval x rho in let a2 = eval y rho in 
                        begin
                          match (a1,a2) with (BoolVal (b1), BoolVal (b2)) -> if b1=b2 then BoolVal (true) else BoolVal (false) 
                            | (NumVal i1, NumVal i2) -> BoolVal (i1 = i2)
                            | _-> raise InvalidExptree
                        end
    | GreaterTE (x,y) -> let a1 = eval x rho in let a2 = eval y rho in 
                        begin
                          match (a1,a2) with (NumVal n1, NumVal n2) -> BoolVal ( n1 >= n2)
                          | _-> raise InvalidExptree
                        end
    | LessTE (x,y) -> let a1 = eval x rho in let a2 = eval y rho in 
                         begin
                          match (a1,a2) with (NumVal n1, NumVal n2) -> BoolVal ( n1  <= n2)
                          | _-> raise InvalidExptree
                        end
    | GreaterT (x,y) -> let a1 = eval x rho in let a2 = eval y rho in 
                        begin
                          match (a1,a2) with (NumVal n1, NumVal n2) -> BoolVal ( n1 > n2)
                          | _-> raise InvalidExptree
                        end
    | LessT (x,y) -> let a1 = eval x rho in let a2 = eval y rho in 
                        begin
                          match (a1,a2) with (NumVal n1, NumVal n2) -> BoolVal (n1 < n2)
                          | _-> raise InvalidExptree
                        end
    | InParen (x) -> eval x rho
    | IfThenElse (x,y,z) -> let a1 = eval x rho in 
                          begin
                          match a1 with BoolVal b1 -> begin 
                                                      if b1 then eval y rho
                                                      else eval z rho
                                                      end
                              | _-> raise InvalidExptree
                          end
    | Tuple (x,y) -> if x = (List.length y) then 
                                        let rec mapp y = 
                                        match y with 
                                                [] -> []
                                              | hd::tls -> (eval hd rho)::(mapp tls) in
                                            TupVal (x,mapp y)
                    else raise InvalidExptree
    | Project ((x,y),z) ->   if (x>0 && x<=y) then
                                                    begin match z with Tuple (a,b) -> if a=y then 
                                                                                eval (List.nth b (x-1)) rho
                                                                                else  raise InvalidExptree
                                                          | Var (a) -> let sval = rho a in
                                                                    begin match sval with 
                                                                      TupVal(b,c)->
                                                                        if b=y then 
                                                                          (List.nth c (x-1)) 
                                                                          else raise InvalidExptree
                                                                      |_ -> raise InvalidExptree
                                                                    end
                                                          | _ -> raise InvalidExptree
                                                    end
                                              else  raise InvalidExptree
    | Let (d,e) -> raise Not_implemented
    | FunctionAbstraction (s,e) -> raise Not_implemented
    | FunctionCall (e1,e2) -> begin
          match e1 with FunctionAbstraction ((s,t),e) ->
          let v1 = eval e2 rho in
          let rho1 s1 = if s1=s then v1 else rho s1 in
          eval e1 rho1
        |_ -> raise Not_implemented
      end
                        
exception EmptyExpression
exception IllFormedOCL

let stackmc stk rho pgm = 
let  sym = (Neg,[]) in
let rec stkmc stk rho pgm = match pgm with [] -> 
begin match stk with a::(b::stks) -> begin match b with Num ((Neg,[])) -> a | _ -> raise IllFormedOCL end
  | _ -> raise IllFormedOCL
end
| px::pxs->
match px with 
    | VAR x -> stkmc ((rho x)::stk) rho pxs
    | NCONST x -> stkmc ((Num x)::stk) rho pxs
    | BCONST x -> stkmc ((Bool x)::stk) rho pxs
    | NOT -> begin 
                match stk with a::(stks) -> 
                    begin   
                      match a with Bool x -> stkmc ((Bool (not x))::(stks)) rho pxs
                      | _ -> raise IllFormedOCL 
                    end 
                    | _ -> raise IllFormedOCL
              end
    | UNARYMINUS ->  begin 
                     match stk with a::(stks) -> 
                        begin 
                          match a with Num x -> stkmc ((Num (minus x))::(stks)) rho pxs
                          | _ -> raise IllFormedOCL 
                        end 
                    | _ -> raise IllFormedOCL
              end
    | ABS -> begin 
                   match stk with a::(stks) -> 
                  begin 
                      match a with Num x -> stkmc ((Num (abs x))::(stks)) rho pxs
                      | _ -> raise IllFormedOCL 
                    end 
                | _ -> raise IllFormedOCL
              end
    | PAREN -> begin
                  match stk with a::(stks) -> 
                      begin match a with Num ((Neg,[])) ->  raise IllFormedOCL
                            | _ -> stkmc stk rho pxs
                      end
                    | _ -> raise IllFormedOCL
              end
    | PLUS -> begin
                  match stk with a::(b::(stks)) -> 
                      begin 
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                                                                else stkmc ((Num (add x y))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            
                      end
                    | _ -> raise IllFormedOCL
              end
    | MINUS -> begin
                  match stk with a::(b::(stks)) -> 
                      begin
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Num (sub y x))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | MULT -> begin
                  match stk with a::(b::(stks)) -> 
                      begin
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Num (mult x y))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            
                      end
                    | _-> raise IllFormedOCL
              end
    | DIV -> begin
                    match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Num (div y x))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | REM -> begin
                     match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Num (rem y x))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | CONJ -> begin
                       match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Bool x,Bool y) -> stkmc ((Bool (x && y))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _ -> raise IllFormedOCL
              end
    | DISJ ->  begin
                    match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Bool x,Bool y) -> stkmc ((Bool (x || y))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | EQS -> begin
                   match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Bool x,Bool y) -> stkmc ((Bool (x = y))::(stks)) rho pxs
                                                              | (Num x, Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Bool (eq y x))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | GTE -> begin
                     match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Bool (geq y x))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | GT -> begin
                     match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Bool (gt y x))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | LTE -> begin
                  match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Bool (leq y x))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | LT -> begin
                   match stk with a::(b::(stks)) -> 
                    begin 
                                                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise IllFormedOCL
                                                              else stkmc ((Bool (lt y x))::(stks)) rho pxs
                                                              | _ -> raise IllFormedOCL 
                                                            end
                            
                    | _-> raise IllFormedOCL
              end
    | TUPLE (x) -> begin
                      let rec checktup ll n ll1 =
                          if n<0 then raise IllFormedOCL else
                          match ll with [] -> raise IllFormedOCL
                          | llx::llxs -> if n=0 then (ll,ll1) else
                            begin match llx with Num (Neg,[]) -> raise IllFormedOCL
                                  | _ -> checktup llxs (n-1) (llx::ll1)
                            end
                      in
                      let (u,v) = checktup stk x [] in
                      stkmc ((Tup (x,v))::u) rho pxs
                    end
    | IFTE -> begin
                  match stk with (a::(b::(c::(stks)))) ->
                      begin 
                                                              match (c) with (Bool x) -> if x then stkmc ((b)::(stks)) rho pxs
                                                                                                            else stkmc ((a)::(stks)) rho pxs                                             
                                                              | _ -> raise IllFormedOCL 
                                                          end 
                          
                    | _ -> raise IllFormedOCL 
              end
    | PROJ (x,y) -> begin
                      match stk with (a::(stks)) ->
                         begin
                                                                match a with Tup (z,w) -> if (y=z) then stkmc ((List.nth w (x-1))::(stks)) rho pxs
                                                                                          else raise IllFormedOCL
                                                                | _ -> raise IllFormedOCL 
                                                            end
                        
                     | _ -> raise IllFormedOCL 
                    end
    | LET -> raise Not_implemented
    | FABS -> raise Not_implemented
    | FCALL -> raise Not_implemented
    | SIMPLEDEF -> raise Not_implemented
    | SEQCOMPOSE -> raise Not_implemented
    | PARCOMPOSE -> raise Not_implemented
    | LOCALDEF -> raise Not_implemented

in 
stkmc ((Num sym)::stk) rho pgm

  
let compile ex = 
  let rec compl ex ll  = match ex with 
    | Var x -> (VAR x)::ll
    | N x -> (NCONST (mk_big x))::ll
    | B x -> (BCONST x)::ll
    | Sub (x,y) -> compl x (compl y (MINUS::ll))
    | Add (x,y) -> compl x (compl y (PLUS::ll))
    | Mult (x,y) -> compl x (compl y (MULT::ll))
    | Div (x,y) -> compl x (compl y (DIV::ll))
    | Rem (x,y) -> compl x (compl y (REM::ll))
    | Not x -> compl x (NOT::ll)
    | Conjunction (x,y) -> compl x (compl y (CONJ::ll))
    | Disjunction (x,y) -> compl x (compl y (DISJ::ll))
    | Equals (x,y) -> compl x (compl y (EQS::ll))
    | GreaterTE (x,y) -> compl x (compl y (GTE::ll))
    | LessTE (x,y) -> compl x (compl y (LTE::ll))
    | GreaterT (x,y) -> compl x (compl y (GT::ll))
    | LessT (x,y) -> compl x (compl y (LT::ll))
    | Negative (x) -> compl x (UNARYMINUS::ll)
    | Abs (x) -> compl x (ABS::ll)
    | InParen x -> compl x (PAREN::ll)
    | IfThenElse (x,y,z) -> compl x (compl y (compl z (IFTE::ll))) 
    | Tuple (x,y) -> let rec joinlists expl l1 =
                      match expl with [] -> l1
                      | expx::expxs -> compl expx (joinlists expxs l1) in
                      joinlists y ((TUPLE (x))::ll)
    | Project ((x,y),z) -> compl z ((PROJ (x,y))::ll)
    | Let (d,e) -> raise Not_implemented
    | FunctionAbstraction (s,e) -> raise Not_implemented
    | FunctionCall (e1,e2) -> raise Not_implemented
    
  in compl ex []





