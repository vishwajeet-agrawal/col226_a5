open A0
open A1

exception InvalidExptree
exception InvalidDefinition
exception Not_implemented
exception Insufficient_TA

let rec extract_l st_e st = match st_e with [] -> raise Insufficient_TA
            | ((a,b))::xs -> 
            if compare st a = 0 then b
            else extract_l xs st
let rec exists_l st_e st = match st_e with [] -> false
            | ((a,b))::xs -> 
            if compare st a = 0 then true
            else exists_l xs st 
let rec check_disjoint d1 d2 =
  if d2 = [] then true else
  let rec check_disjoint1 x d2t=
              match d2t with [] -> true
                | (y,e2)::ys -> if x=y then false else check_disjoint1 x ys 
              
              in
  match d1 with [] -> true 
  | (x,e)::xs -> if check_disjoint1 x d2 then check_disjoint xs d2 else false
              
let rec substitute_lx f lx x =

let rec get_defined_v d xl = begin
    match d with 
      |Simple((s,t),e) -> let c = substitute_lx e xl [] in [(s,c)]
      |Simple_untyped(s,e)     -> let c = substitute_lx e xl [] in [(s,c)]
      |Sequence (dl)  -> 
        let rec def_seq_v dl uvar dvar =
    
        begin
        match dl with [] ->  dvar
          | dlx::dlxs    -> let d1 = get_defined_v dlx uvar  in
                            def_seq_v dlxs (List.append d1 uvar) (List.append d1 dvar)
                            (* let d2 = get_defined_v (Sequence(dlxs)) (List.append d1 xl) in
                            List.append d2 d1 *)
        end in def_seq_v dl xl [] 
    
      |Parallel (dl)  -> begin
        match dl with [] ->  xl
          | dlx::dlxs    -> let dv1 = get_defined_v dlx xl in
                            let dv2 = get_defined_v (Parallel(dlxs)) xl in
                            if check_disjoint dv1 dv2 then List.append dv1 dv2 else raise InvalidDefinition
        end
    
      | Local (d1,d2) -> let d11 = get_defined_v d1 xl in get_defined_v d2 (List.append d11 xl)
      
    end 
  in

  match f with 
  Var a  ->  let p b = (compare b a = 0) in if List.exists p x then f else if exists_l lx a then extract_l lx a else f  (* variables starting with a Capital letter, represented as alphanumeric strings with underscores (_) and apostrophes (') *)
  | N a ->  f     (* Integer constant *)
  | B a -> f    (* Boolean constant *)
  (* unary operators on integers *)
  | Abs a -> Abs (substitute_lx a lx x)                   (* abs *)
  | Negative a -> Negative (substitute_lx a lx x)              (* unary minus ~ *)
  (* unary operators on booleans *)
  | Not a -> Not (substitute_lx a lx x )
  (* binary operators on integers *)
  | Add (a,b) -> Add (substitute_lx a lx x ,substitute_lx b lx x )         (* Addition + *)
  | Sub (a,b) -> Sub (substitute_lx a lx x ,substitute_lx b lx x)      (* Subtraction - *)
  | Mult (a,b) -> Mult (substitute_lx a lx x ,substitute_lx b lx x)       (* Multiplication * *)
  | Div (a,b) -> Div (substitute_lx a lx x ,substitute_lx b lx x)         (* div *)
  | Rem (a,b) -> Rem (substitute_lx a lx x ,substitute_lx b lx x)        (* mod *)
  (* binary operators on booleans *)
  | Conjunction (a,b) -> Conjunction (substitute_lx a lx x ,substitute_lx b lx x) (* conjunction /\ *)
  | Disjunction (a,b) -> Disjunction (substitute_lx a lx x ,substitute_lx b lx x) (* binary operators on booleans \/ *)
  (* comparison operations on integers *)
  | Equals (a,b) -> Equals (substitute_lx a lx x ,substitute_lx b lx x)      (* = *)
  | GreaterTE (a,b) -> GreaterTE (substitute_lx a lx x ,substitute_lx b lx x)   (* >= *)
  | LessTE (a,b) -> LessTE (substitute_lx a lx x ,substitute_lx b lx x)      (* <= *)
  | GreaterT (a,b) -> GreaterT (substitute_lx a lx x ,substitute_lx b lx x)    (* > *)
  | LessT (a,b) -> LessT (substitute_lx a lx x ,substitute_lx b lx x)       (* < *)
  (* expressions using parenthesis *)
  | InParen a -> InParen (substitute_lx a lx x)               (* ( ) *)
  (* a conditional expression *)
  | IfThenElse (a,b,c) -> IfThenElse (substitute_lx a lx x ,substitute_lx b lx x,substitute_lx c lx x)  (* if then else fi  *)
  (* creating n-tuples (n >= 0) *)
  | Tuple (a,b) -> let sub_xe a = substitute_lx a lx x in Tuple (a,List.map sub_xe b)
  (* projecting the i-th component of an expression (which evaluates to an n-tuple, and 1 <= i <= n) *)
  | Project ((a,b),c) -> Project ((a,b),substitute_lx c lx x)   (* Proj((i,n), e)  0 < i <= n *)
  | Let (a,b) -> let vbls1 = get_defined_v a [] in 
                  let apl = List.append vbls1 lx in
                  substitute_lx b apl x
  | FunctionAbstraction ((a,t),b) -> FunctionAbstraction((a,t),substitute_lx b lx (a::x))
  | FunctionCall (a,b) -> FunctionCall (substitute_lx a lx x,substitute_lx b lx x)




  (* hastype : ((string * exptype) list) -> exptree -> exptype -> bool *)

  (* Output list containes (string,exp) where variables in exp are free variables contained in Y (string -> answer):= (binding rho) *)
(* get_defined_v gives string * exptree list *)
let rec get_defined_v d xl = begin
  match d with
  |Simple((s,t),e) ->   let c = substitute_lx e xl [] in [(s,c)]
  |Simple_untyped(s,e)     -> let c = substitute_lx e xl [] in [(s,c)]
  |Sequence (dl)  -> 
    let rec def_seq_v dl uvar dvar =

  begin
  match dl with [] ->  dvar
    | dlx::dlxs    -> let d1 = get_defined_v dlx uvar  in
                      def_seq_v dlxs (List.append d1 uvar) (List.append d1 dvar)
                      (* let d2 = get_defined_v (Sequence(dlxs)) (List.append d1 xl) in
                      List.append d2 d1 *)
  end in def_seq_v dl xl [] 

  |Parallel (dl)  -> begin
    match dl with [] ->  xl
    | dlx::dlxs    -> let dv1 = get_defined_v dlx xl in
                      let dv2 = get_defined_v (Parallel(dlxs)) xl in
                      if check_disjoint dv1 dv2 then List.append dv1 dv2 else raise InvalidDefinition
  end

| Local (d1,d2) -> let d11 = get_defined_v d1 xl in get_defined_v d2 (List.append d11 xl)

end 
let rec eliminate_dups din dout =
  match din with [] -> dout
  | (s,dx)::dxs -> if exists_l dout s then eliminate_dups dxs dout 
  else eliminate_dups dxs ((s,dx)::dout)

let check_disjoint dx1 dx2 =
let d1 = eliminate_dups dx1 [] in
let d2 = eliminate_dups dx2 [] in
let rec check_disjointd d1 d2 =
if d2 = [] then true else
let rec check_disjoint1 x d2t=
            match d2t with [] -> true
              | (y,e2)::ys -> if x=y then false else check_disjoint1 x ys 
in
match d1 with [] -> true 
| (x,e)::xs -> if check_disjoint1 x d2 then check_disjointd xs d2 else false
in check_disjointd d1 d2 && check_disjointd d2 d1


let rec checkcontains d1 d2 =
  match d1 with [] ->true
  |(s,t)::d1s -> if exists_l d2 s then extract_l d2 s = t &&  checkcontains d1s d2 else false



            

let rec infertype g e =
  let rec definedvar_type g d = 
    match d with 
      Simple((s,t),e1)     -> if infertype g e1 = t then [(s,t)] else raise InvalidDefinition
      |Simple_untyped (s,e1) -> [(s,infertype g e1)]
      |Sequence (dl)  -> 
        let rec def_seq_v dl uvar dvar =
    
        begin
        match dl with [] ->  dvar
          | dlx::dlxs    -> let d1 = definedvar_type uvar dlx  in
                            def_seq_v dlxs (List.append d1 uvar) (List.append d1 dvar)
                            (* let d2 = get_defined_v (Sequence(dlxs)) (List.append d1 xl) in
                            List.append d2 d1 *)
        end in def_seq_v dl g [] 
    
      |Parallel (dl)  -> begin
        match dl with [] ->  []
          | dlx::dlxs    -> let dv1 = definedvar_type g dlx in
                            let dv2 = definedvar_type g (Parallel(dlxs)) in
                            if check_disjoint dv1 dv2 then List.append dv1 dv2 else raise InvalidDefinition
        end
    
      | Local (d1,d2) -> let d11 = definedvar_type g d1 in definedvar_type (List.append d11 g) d2
  in    
  match e with 
  N a -> Tint
  | B a -> Tbool
  | Var x -> if exists_l g x then extract_l g x else Tvar (x)
  | Abs a 
  | Negative a -> if infertype g a = Tint then Tint else raise InvalidExptree
  | Add(x,y) | Sub(x,y) | Mult(x,y) | Rem(x,y) | Div(x,y) -> 
  if infertype g x = Tint && infertype g y = Tint then Tint else raise InvalidExptree
  | Not a -> if infertype g a = Tbool then Tbool else raise InvalidExptree
  | Conjunction(x,y) | Disjunction(x,y) ->  
  if infertype g x = Tbool && infertype g y = Tbool then Tbool else raise InvalidExptree
  | Equals (x,y) ->
  if infertype g x = infertype g y then Tbool else raise InvalidExptree
  | GreaterTE(x,y) | LessTE(x,y) | GreaterT(x,y) | LessT (x,y) ->
  if infertype g x = Tint && infertype g y = Tint then Tbool else raise InvalidExptree
  | InParen x -> infertype g x
  | IfThenElse (x,y,z) ->
  if infertype g x = Tbool then 
    let ans = infertype g y in
    if ans = infertype g z then ans 
    else raise InvalidExptree
  else raise InvalidExptree
  | Tuple(n,exl) -> 
    if n<2 then raise InvalidExptree
    else if List.length exl = n then
      let rec inf_type exl = 
      match exl with [] -> []
      | ex1::exs1 -> let t1 = infertype g ex1 in
        t1::(inf_type exs1) in
      let tl = inf_type exl in
       Ttuple(tl)
    else raise InvalidExptree
  |Project((a,b),c) -> 
  if a <1 || b<2  || a>b then raise InvalidExptree
  else
    let t1 = infertype g c in begin
    match t1 with Ttuple (tl) ->
    if List.length tl = b then List.nth tl (a-1) else raise InvalidExptree
    | _ -> raise InvalidExptree end
  |FunctionAbstraction((s,tp),ex) ->
    let t1 = infertype ((s,tp)::g) ex in
    Tfunc(tp,t1)

  |FunctionCall (e1,e2) ->
    let t1 = infertype g e1 in begin
    match t1 with Tfunc (t2,t3) -> if infertype g e2 = t2 then t3 else raise InvalidExptree
    | _-> raise InvalidExptree
    end

  |Let (d,e1) ->
  let dv1 =  definedvar_type g d in
  infertype (List.append dv1 g) e1




  let rec definedvar_type g d = 
    match d with 
      Simple((s,t),e)     -> if infertype g e = t then [(s,t)] else raise InvalidDefinition
      |Simple_untyped (s,e1) -> [(s,infertype g e1)]
      |Sequence (dl)  -> 
        let rec def_seq_v dl uvar dvar =
    
        begin
        match dl with [] ->  dvar
          | dlx::dlxs    -> let d1 = definedvar_type uvar dlx  in
                            def_seq_v dlxs (List.append d1 uvar) (List.append d1 dvar)
                            (* let d2 = get_defined_v (Sequence(dlxs)) (List.append d1 xl) in
                            List.append d2 d1 *)
        end in def_seq_v dl g [] 
    
      |Parallel (dl)  -> begin
        match dl with [] ->  []
          | dlx::dlxs    -> let dv1 = definedvar_type g dlx in
                            let dv2 = definedvar_type g (Parallel(dlxs)) in
                            if check_disjoint dv1 dv2 then List.append dv1 dv2 else raise InvalidDefinition
        end
    
      | Local (d1,d2) -> let d11 = definedvar_type g d1 in definedvar_type (List.append d11 g) d2


let hastype g e t = 
  try
  let t1 = infertype g e in
  if t = Tunit || t = t1 then true else false
  with InvalidExptree | InvalidDefinition -> false

let yields g d g_dash = 
  let tl1 = definedvar_type g d in
  let dx1 = eliminate_dups tl1 [] in
    checkcontains dx1 g_dash && checkcontains g_dash dx1
  
  let rec exptoclosure el gl=
    match el with [] -> []
    | (s,e)::els -> (s,Clos(e,gl))::(exptoclosure els gl)

let rec get_dvbls_closure d closl = 
  match d with 
  Simple_untyped(s,e) -> [(s,Clos(e,closl))]
  |Simple((s,t),e) -> [(s,Clos(e,closl))]
  |Sequence(dl) -> 
  let rec def_seq_v dl uvar dvar =
    begin
    match dl with [] ->  dvar
      | dlx::dlxs    -> let d1 = get_dvbls_closure dlx uvar  in
                        def_seq_v dlxs (List.append d1 uvar) (List.append d1 dvar)
                        (* let d2 = get_defined_v (Sequence(dlxs)) (List.append d1 xl) in
                        List.append d2 d1 *)
    end in def_seq_v dl closl [] 
  |Parallel(dl) -> begin
    match dl with [] ->  []
      | dlx::dlxs    -> let dv1 = get_dvbls_closure dlx closl in
                        let dv2 = get_dvbls_closure (Parallel(dlxs)) closl in
                        if check_disjoint dv1 dv2 then List.append dv1 dv2 else raise InvalidDefinition
    end
  |Local (d1,d2) -> get_dvbls_closure d2 (List.append (get_dvbls_closure d1 closl) closl)

let rec infertype_closure g cl = 
  let rec get_type_explist exl = 
    match exl with [] -> g
    | (s,cl1)::erl -> (s,infertype_closure g cl1)::(get_type_explist erl)
  in 
  match cl with Clos (e,clt) -> infertype (get_type_explist clt) e
 
(* let rec infertype_answer g ans =
  match ans with 
  Num (n) -> Tint
  | Bool b -> Tbool
  | Tup (n,t) -> let rec ital g al = match al with [] -> [] | al1::als-> (infertype_answer g al1)::(ital g als) in
                Ttuple(ital g t)
  | Fun ((s,t),a)-> Tfun(t,infertype ((s,t)::g) t)
  | VClos (e,al) -> ( match al with [] -> (infertype g e)
                      | (s,an)::als -> infertype_answer ((s,infertype_answer g an)::g) (VClos(e,als)) ) *)

  exception InvalidMachine
 type krivineopcode =
  KADD | KMULT | KSUB | KEQ | KGE | KGT | KLT | KLE | KABS | KNOT | KNEG | KDIV | KREM  | KIFTE |KAND | KOR| CLOS of closure 


  let rec krivine_machine_in clos stk = 
    match clos with Clos(e,closl) ->
    begin match e with 
      |Var x -> krivine_machine_in (extract_l closl x) stk 
      |IfThenElse(x,y,z) ->
        krivine_machine_in (Clos(x,closl)) ((CLOS(Clos(y,closl)))::((CLOS(Clos(z,closl)))::KIFTE::stk))
      |N x -> begin
        match stk with [] -> NumVal (x)
        | (CLOS(stk1))::(KADD::stks) -> let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(N (x+y),[])) stks  | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KSUB::stks) -> let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(N (x-y),[])) stks  | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KDIV::stks) -> let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(N (x/y),[])) stks  | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KREM::stks) -> let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(N (x mod y),[])) stks  | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KMULT::stks) -> let a1 = krivine_machine_in stk1 [] in
        (match a1 with NumVal(y) ->krivine_machine_in (Clos(N (x*y),[])) stks | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KEQ::stks) ->  let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(B (x=y),[])) stks   | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KGT::stks) ->  let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(B (x>y),[])) stks   | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KGE::stks) ->  let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(B (x>=y),[])) stks   | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KLT::stks) ->  let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(B (x<y),[])) stks   | _-> raise InvalidMachine)
        | (CLOS(stk1))::(KLE::stks) ->  let a1 = krivine_machine_in stk1 [] in 
        (match a1 with NumVal(y) -> krivine_machine_in (Clos(B (x<=y),[])) stks   | _-> raise InvalidMachine)
        | KNEG::stks -> krivine_machine_in (Clos (N (-x),[])) stks
        | KABS::stks -> krivine_machine_in (Clos (N (if x<0 then -x else x),[])) stks
        | _-> raise InvalidMachine
      end
    |B x -> begin
      match stk with [] -> BoolVal (x)
      | (CLOS(stk1))::(CLOS(stk2)::KIFTE::stks) -> if x then krivine_machine_in stk1 stks else krivine_machine_in stk2 stks
      | (CLOS(stk1))::(KEQ::stks) ->  let a1 = krivine_machine_in stk1 [] in 
      (match a1 with BoolVal(y) -> krivine_machine_in (Clos(B (x=y),[])) stks   | _-> raise InvalidMachine)
      | (CLOS(stk1))::(KAND::stks) ->  let a1 = krivine_machine_in stk1 [] in 
      (match a1 with BoolVal(y) -> krivine_machine_in (Clos(B (x && y),[])) stks   | _-> raise InvalidMachine)
      | (CLOS(stk1))::(KOR::stks) ->  let a1 = krivine_machine_in stk1 [] in 
      (match a1 with BoolVal(y) -> krivine_machine_in (Clos(B (x || y),[])) stks   | _-> raise InvalidMachine)
      | KNOT::stks -> krivine_machine_in (Clos(B (not x),[])) stks
      | _-> raise InvalidMachine
    end
    |Add (x,y) -> krivine_machine_in (Clos(x,closl)) ((CLOS(Clos(y,closl)))::KADD::stk)
    |Mult (x,y) -> krivine_machine_in (Clos(x,closl)) ((CLOS(Clos(y,closl)))::KMULT::stk)
    |Div (x,y) -> krivine_machine_in (Clos(x,closl)) ((CLOS(Clos(y,closl)))::KDIV::stk)
    |Rem (x,y) -> krivine_machine_in (Clos(x,closl)) ((CLOS(Clos(y,closl)))::KREM::stk)
    |Sub (x,y) -> krivine_machine_in (Clos(x,closl)) ((CLOS(Clos(y,closl)))::KSUB::stk)
    |FunctionCall (x,y) -> krivine_machine_in (Clos(x,closl)) ((CLOS(Clos(y,closl)))::stk)
    |FunctionAbstraction ((s,t),e) -> begin
      match stk with 
      [] -> let kml (s,cl) = (s,krivine_machine_in cl []) in
      FunVal (s,Vclosure(e,List.map kml closl ))
      | CLOS(stk1)::stks -> krivine_machine_in (Clos(e,(s,stk1)::closl)) stks 
      | _-> raise InvalidMachine
    end
    | Let(d,e) -> krivine_machine_in (Clos(e,(List.append (get_dvbls_closure d closl) closl))) stk
    | Equals (e1,e2) -> krivine_machine_in (Clos(e1,closl)) (CLOS(Clos(e2,closl))::KEQ::stk)
    | GreaterTE (e1,e2) -> krivine_machine_in (Clos(e1,closl)) (CLOS(Clos(e2,closl))::KGE::stk)
    | LessTE (e1,e2) -> krivine_machine_in (Clos(e1,closl)) (CLOS(Clos(e2,closl))::KLE::stk)
    | GreaterT (e1,e2) -> krivine_machine_in (Clos(e1,closl)) (CLOS(Clos(e2,closl))::KGT::stk)
    | LessT (e1,e2) -> krivine_machine_in (Clos(e1,closl)) (CLOS(Clos(e2,closl))::KLT::stk)
    | Negative (e1) -> krivine_machine_in (Clos(e1,closl)) (KNEG::stk)
    | Not (e1) -> krivine_machine_in (Clos(e1,closl)) (KNOT::stk)
    | Abs (e1) -> krivine_machine_in (Clos(e1,closl)) (KABS::stk)
    | InParen (e1) -> krivine_machine_in (Clos(e1,closl)) stk
    | Conjunction (e1,e2) -> krivine_machine_in (Clos(e1,closl)) (CLOS(Clos(e2,closl))::KAND::stk)
    | Disjunction (e1,e2) -> krivine_machine_in (Clos(e1,closl)) (CLOS(Clos(e2,closl))::KOR::stk)
    | Project((i,n),e) -> raise Not_implemented
    | Tuple (n,el) -> raise Not_implemented

  end

let rec krivine_machine clos stk= 
  toAnswer (krivine_machine_in clos stk)

let numsym = Num ((Neg,[]));;
let sym = (Neg,[]);;
let secd_machine stk env pgm dump=
let rec secdmachine stk env pgm dump = 
  match pgm with [] ->
  ( match stk with 
  [] -> raise InvalidMachine
  |stx::[] -> raise InvalidMachine
  |stx::sym1::stxs -> if sym1 = numsym && (not (stx = numsym)) then stx else  raise InvalidMachine)
   

    | pgx::pxs ->
      begin
        match pgx with 
    2    | VAR x -> secdmachine ((extract_l env x)::stk) env pxs dump 
        | NCONST x -> secdmachine ((Num x)::stk) env pxs dump
        | BCONST x -> secdmachine ((Bool x)::stk) env pxs dump
        | NOT -> begin 
                    match stk with a::(stks) -> 
                        begin   
                          match a with Bool x -> secdmachine ((Bool (not x))::(stks)) env pxs dump
                          | _ -> raise InvalidMachine 
                        end 
                        | _ -> raise InvalidMachine
                  end
        | UNARYMINUS ->  begin 
                        match stk with a::(stks) -> 
                            begin 
                              match a with Num x -> if (eq x sym) then raise InvalidMachine
                          else secdmachine ((Num (minus x))::(stks)) env pxs dump
                              | _ -> raise InvalidMachine 
                            end 
                        | _ -> raise InvalidMachine
                  end
        | ABS -> begin 
                      match stk with a::(stks) -> 
                      begin 
                          match a with Num x ->  if (eq x sym) then raise InvalidMachine
                          else secdmachine ((Num (abs x))::(stks)) env pxs dump
                          | _ -> raise InvalidMachine 
                        end 
                    | _ -> raise InvalidMachine
                  end
        | PAREN -> secdmachine stk env pxs dump
        | PLUS -> begin
                      match stk with a::(b::(stks)) -> 
                          begin 
                                                                  match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                                                                                                    else secdmachine ((Num (add x y))::(stks)) env pxs dump
                                                                  | _ -> raise InvalidMachine 
                                                                
                          end
                        | _ -> raise InvalidMachine
                  end
        | MINUS -> begin
                      match stk with a::(b::(stks)) -> 
                          begin
                            match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                            else secdmachine ((Num (sub y x))::(stks)) env pxs dump
                            | _ -> raise InvalidMachine 
                          end
                                
                        | _-> raise InvalidMachine
                  end
        | MULT -> begin
                      match stk with a::(b::(stks)) -> 
                          begin
                            match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                            else secdmachine ((Num (mult x y))::(stks)) env pxs dump
                            | _ -> raise InvalidMachine 
                                                                
                          end
                        | _-> raise InvalidMachine
                  end
        | DIV -> begin
                        match stk with a::(b::(stks)) -> 
                        begin 
                          match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                          else secdmachine ((Num (div y x))::(stks)) env pxs dump
                          | _ -> raise InvalidMachine 
                        end
                                
                        | _-> raise InvalidMachine
                  end
        | REM -> begin
                        match stk with a::(b::(stks)) -> 
                        begin 
                            match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                            else secdmachine ((Num (rem y x))::(stks)) env pxs dump
                            | _ -> raise InvalidMachine 
                          end
                                
                        | _-> raise InvalidMachine
                  end
        | CONJ -> begin
                          match stk with a::(b::(stks)) -> 
                        begin 
                            match (a,b) with (Bool x,Bool y) -> secdmachine ((Bool (x && y))::(stks)) env pxs dump
                            | _ -> raise InvalidMachine 
                          end
                                
                        | _ -> raise InvalidMachine
                  end
        | DISJ ->  begin
                        match stk with a::(b::(stks)) -> 
                        begin 
                              match (a,b) with (Bool x,Bool y) -> secdmachine ((Bool (x || y))::(stks)) env pxs dump
                              | _ -> raise InvalidMachine 
                            end
                                
                        | _-> raise InvalidMachine
                  end
        | EQS -> begin
                      match stk with a::(b::(stks)) -> 
                        begin 
                            match (a,b) with (Bool x,Bool y) -> secdmachine ((Bool (x = y))::(stks)) env pxs dump
                            | (Num x, Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                            else secdmachine ((Bool (eq y x))::(stks)) env pxs dump
                            | _ -> raise InvalidMachine 
                          end
                                
                        | _-> raise InvalidMachine
                  end
        | GTE -> begin
                        match stk with a::(b::(stks)) -> 
                        begin 
                                match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                                else secdmachine ((Bool (geq y x))::(stks)) env pxs dump
                                | _ -> raise InvalidMachine 
                              end
                                
                        | _-> raise InvalidMachine
                  end
        | GT -> begin
                        match stk with a::(b::(stks)) -> 
                        begin 
                                match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                                else secdmachine ((Bool (gt y x))::(stks)) env pxs dump
                                | _ -> raise InvalidMachine 
                              end
                                
                        | _-> raise InvalidMachine
                  end
        | LTE -> begin
                      match stk with a::(b::(stks)) -> 
                        begin 
                        match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                        else secdmachine ((Bool (leq y x))::(stks)) env pxs dump
                        | _ -> raise InvalidMachine 
                      end
                                
                        | _-> raise InvalidMachine
                  end
        | LT -> begin
                      match stk with a::(b::(stks)) -> 
                        begin 
                              match (a,b) with (Num x,Num y) -> if (eq x sym || (eq y sym)) then raise InvalidMachine
                              else secdmachine ((Bool (lt y x))::(stks)) env pxs dump
                              | _ -> raise InvalidMachine 
                            end
                                
                        | _-> raise InvalidMachine
                  end
        | TUPLE (x) -> begin
                          let rec checktup ll n ll1 =
                              if n<0 then raise InvalidMachine else
                              match ll with [] -> raise InvalidMachine
                              | llx::llxs -> if n=0 then (ll,ll1) else
                                begin match llx with Num (Neg,[]) -> raise InvalidMachine
                                      | _ -> checktup llxs (n-1) (llx::ll1)
                                end
                          in
                          let (u,v) = checktup stk x [] in
                          secdmachine ((Tup (x,v))::u) env pxs dump
                        end
        | IFTE (y,z)  -> begin
                      match stk with (a::(stks)) ->
                          begin 
                        match (a) with (Bool x) -> if x then secdmachine stks env (List.append y pxs) dump
                                                    else secdmachine stks env (List.append z pxs) dump                                         
                        | _ -> raise InvalidMachine 
                        end 
                              
                        | _ -> raise InvalidMachine 
                  end
        | PROJ (x,y) -> begin
                          match stk with (a::(stks)) ->
                            begin
                                match a with Tup (z,w) -> if (y=z) then secdmachine ((List.nth w (x-1))::(stks)) env pxs dump
                                                          else raise InvalidMachine
                                | _ -> raise InvalidMachine 
                            end
                            
                        | _ -> raise InvalidMachine 
                        end
        | LET -> raise Not_implemented
        | FABS (s,ocl) -> secdmachine (Fun (s,VClos(ocl,env))::stk) env pxs dump            
        | FCALL ->  begin
          match stk with (a::b::(stks)) ->
          if a = numsym || b = numsym then raise InvalidMachine
          else
          begin match b with Fun (s,VClos(ocl,envl)) -> 
            secdmachine (numsym::[]) ((s,a)::envl) ocl ((stks,env,pxs)::dump)
            |_-> raise InvalidMachine
          end
          |_-> raise InvalidMachine
        end
      
        | SIMPLEDEF (s)-> raise Not_implemented
        | SEQCOMPOSE -> raise Not_implemented
        | PARCOMPOSE -> raise Not_implemented
        | LOCALDEF -> raise Not_implemented
        | RET -> (match stk with a::b::stks -> if (a = numsym || not (b = numsym)) then raise InvalidMachine else
                (match dump with (sa,ea,ca)::dumpx ->
                secdmachine (a::sa) ea ca dumpx
                |_ ->raise InvalidMachine)| _-> raise InvalidMachine)
      end
   
in secdmachine ((Num (Neg,[]))::stk) env pgm dump
