open A1
exception NotImplemented
exception Insufficient_TA
exception InvalidExptree
(* exception Undecidable *)
exception InvalidDefinition
type tclosure = 
  Tclos of exptree * ((string * exptype) list) * ((string * tclosure)  list)

(* Helper functions *)
  (* extract_l gives 'a out of (string * 'a list) *)
(* exists_l checks if string exists in (string * 'a list) *)
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
      Simple(s,e)     -> let c = substitute_lx e xl [] in [(s,c)]
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
  | FunctionAbstraction (a,b) -> FunctionAbstraction(a,substitute_lx b lx (a::x))
  | FunctionCall (a,b) -> FunctionCall (substitute_lx a lx x,substitute_lx b lx x)




  (* hastype : ((string * exptype) list) -> exptree -> exptype -> bool *)

  (* Output list containes (string,exp) where variables in exp are free variables contained in Y (string -> answer):= (binding rho) *)
(* get_defined_v gives string * exptree list *)
let rec get_defined_v d xl = begin
  match d with 
  Simple(s,e)     -> let c = substitute_lx e xl [] in [(s,c)]
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
(* g is string exptype list, gut is string closure list output is a closure map (using list)*)
let rec exptoclosure g gut el =
  match el with [] -> []
  | (s,e)::els -> (s,Tclos(e,g,gut))::(exptoclosure g gut els)
let rec removekeys l1 l2 =
  match l1 with [] -> []
  | (s,v1)::l1xs -> let p (a,b) = a=s in if List.exists p l2 then removekeys l1xs l2 else (s,v1)::(removekeys l1xs l2) 

(* given type hastype checks if big step reduction of a closure is that type *)
(* given a type list yields checks if big step reduction of a  closure list is that type list *)
(* closure is basically a type closure *)


(* Main functions *)
let rec hastype1 c t  = 
  let (e,gt,gut) = match c with Tclos(e,gt,gut)-> (e,gt,gut) in begin
  (* let rec hasoneoftuple g e t i n =
  match e with 
    |Var (x) -> let t1= extract_l g x in
    begin match t1 with Ttuple(typel) -> if List.length typel = n then if List.nth typel (i-1) = t then true else false else false(*raise InvalidExptree*)
        |_-> false(*raise InvalidExptree*) end
    |InParen(x) -> hasoneoftuple g e t i n
    |IfThenElse(x,y,z) -> if hastype g x Tbool then (hasoneoftuple g e t i n) && (hasoneoftuple g e t i n) else false(*raise InvalidExptree*)
    |Tuple (j,xl) -> if j = n then hastype g (List.nth xl (i-1)) t else false(*raise InvalidExptree*)
    |FunctionCall(e1,e2) -> begin match e1 with FunctionAbstraction(s1,ee1) -> hasoneoftuple g (substitute_lx ee1 [(s1,e2)] []) t i n | _-> false(*raise InvalidExptree*) end
    |Let(d1,e1) -> hasoneoftuple g (substitute_lx e1 (get_defined_v d1 []) []) t i n
    | _-> false(*raise InvalidExptree*) 
    in *)
  match e with
  | N x -> if t=Tint then (true,gt,gut) else (false,[],[])
  | B x -> if t=Tbool then (true,gt,gut) else (false,[],[])
  | Var x -> 
    if exists_l gt x then (extract_l gt x = t,gt,gut)
    else if exists_l gut x then 
    let c1 = extract_l gut x in
    hastype1 c1 t
    else (false,[],[])
  | Add(x,y) | Sub(x,y) | Mult(x,y) | Rem(x,y) | Div(x,y) -> 
    if t=Tint then 
    let (a,b,c) = hastype1 (Tclos(x,gt,gut)) Tint in
    if a then hastype1 (Tclos(y,b,c)) Tint
    else (false,[],[])
    else (false,[],[])
  | Abs(x) | Negative(x) -> 
    if t= Tint then
    hastype1 (Tclos(x,gt,gut)) Tint
    else (false,[],[])
  | Not(x) ->
    if t= Tbool then
    hastype1 (Tclos(x,gt,gut)) Tbool
    else (false,[],[])
  | Conjunction(x,y) | Disjunction(x,y) ->  
    if t=Tbool then 
    let (a,b,c) = hastype1 (Tclos(x,gt,gut)) Tbool in
    if a then hastype1 (Tclos(y,b,c)) Tbool
    else (false,[],[])
    else (false,[],[])
  | Equals (x,y) -> if t=Tbool then 
    let (a,b,c) = hastype1 (Tclos(x,gt,gut)) Tint in
    if a then
    hastype1 (Tclos(y,b,c)) Tint
    else 
    let (a,b,c) = hastype1 (Tclos(y,gt,gut)) Tbool in
    if a then
    hastype1 (Tclos(y,b,c)) Tbool
    else 
    (false,[],[])
    else (false,[],[])
  | GreaterTE(x,y) | LessTE(x,y) | GreaterT(x,y) | LessT (x,y) -> if t=Tbool then 
    let (a,b,c) = hastype1 (Tclos(x,gt,gut)) Tint in
    if a then hastype1 (Tclos(y,b,c)) Tint
    else (false,[],[])
    else (false,[],[])
  | InParen(x) -> hastype1 (Tclos(x,gt,gut)) t
  | IfThenElse(x,y,z) -> 
    let (a,b,c) = hastype1 (Tclos(x,gt,gut)) Tbool in
    if a then 
      let (a1,b1,c1) = hastype1 (Tclos(y,b,c)) t in
      if a1 then 
        hastype1 (Tclos(z,b1,c1)) t
      else (false,[],[])
    else (false,[],[])
  | Tuple(n,x) ->begin
    match t with Ttuple(typel) -> 
      if List.length x = n && List.length typel = n then
        let rec ht1 txl exl gt gut= match txl with
          []->(true,gt,gut)
          |fts::ftsx ->begin
              match exl with 
              []-> (false,[],[]) (*not required though*)
              | fes::fesx -> let(a,b,c) = hastype1 (Tclos(fes,gt,gut)) fts in
              if a then ht1 ftsx fesx b c else (false,[],[])
            end
        in
        ht1 typel x gt gut
      else (false,[],[])
      | _-> (false,[],[])
    end
  | Project((i,n),x) -> 
    let rec hasoneoftuple gt gut e1 t i n=
      match e1 with  
      |Var (x) -> if exists_l gt x then 
        match extract_l gt x with 
        Ttuple(typel1) -> if  n = List.length typel1 then if (List.nth typel1 (i-1))=t then (true,gt,gut) else (false,[],[]) else (false,[],[] )
        |_ -> (false,[],[]) 
        else if exists_l gut x then 
        let (e2,gt2,gut2)= match extract_l gut x with Tclos(q,w,e) -> (q,w,e)  in
        let (a1,b1,c1) = hasoneoftuple gt2 gut2 e2 t i n in
        if a1 then (true,gt,gut)
        else (false,[],[])
        else raise Insufficient_TA

      |InParen(x) -> hasoneoftuple gt gut x t i n
      |IfThenElse(x,y,z) -> 
        let (a,b,c) =  hastype1 (Tclos(x,gt,gut)) Tbool in
        if a then 
          let (a1,b1,c1) = (hasoneoftuple b c y t i n) in
          if a1 then
            (hasoneoftuple b1 c1 z t i n) 
          else (false,[],[])(*raise InvalidExptree*)
        else (false,[],[])
      |Tuple (j,xl) -> if j = n then hastype1 (Tclos((List.nth xl (i-1)),gt,gut)) t else (false,[],[]) (*raise InvalidExptree*)
      |FunctionCall(e2,e3) -> 
        let rec hasoneoftuplef gt gut e1 t i n fex =
          match e1 with 
            FunctionAbstraction(s1,e2)-> raise NotImplemented 
            |Var (x) -> raise NotImplemented
            |FunctionCall(e4,e5) -> raise NotImplemented
            |IfThenElse (e4,e5,e6) -> raise NotImplemented
            |Project((i1,n1),e4) -> raise NotImplemented
            |Let(d,e4) -> raise NotImplemented
            |InParen(e4) -> hasoneoftuplef gt gut e4 t i n fex
            | _ -> (false,[],[])

          in
          hasoneoftuplef gt gut e2 t i n e3
      |Let(d1,e2) -> let c1 = exptoclosure gt gut (get_defined_v d1 []) in
        let (a,b,c) = hasoneoftuple (removekeys gt c1) (List.append c1 gut) e2 t i n in
        if a then (true,(List.append (removekeys b c1) gt),c)
        else (false,[],[])
      | _-> (false,[],[])(*raise InvalidExptree*) 
    in
    hasoneoftuple gt gut x t i n
  | Let(d,x) -> 
    let cl1 = exptoclosure gt gut (get_defined_v d []) in
    let gt1 = removekeys gt cl1 in
    let gut1 = removekeys gut cl1 in 
    let (a,b,c) = hastype1 (Tclos(x,gt1, (List.append cl1 gut1))) t in
    if a then 
        (a,List.append (removekeys b cl1) gt,List.append (removekeys c cl1) gut)
    else (false,[],[])
    
    
  | FunctionCall(e1,pmv) ->
      let rec hastype2 c t fex =
        let (ex1,gt1,gut1) = match c with Tclos(ex1,gt1,gut1) -> (ex1,gt1,gut1) in
        begin
          match ex1 with 
          | Var x -> if exists_l gt1 x then begin
             match extract_l gt1 x with 
             Tfunc(tp1,tp2)-> if t=tp2 then hastype1 (Tclos(fex,gt1,gut1)) tp1 else (false,[],[])
             | _-> (false,[],[])
            end
            else if exists_l gut1 x then begin
              raise NotImplemented
            end
            else raise Insufficient_TA
          | InParen x -> hastype2 (Tclos(x,gt1,gut1)) t fex 
          | IfThenElse (x,y,z) -> 
            let(a,b,c) = hastype1 (Tclos(x,gt1,gut1)) Tbool in
            if a then
              let (a1,b1,c1) = hastype2 (Tclos(y,b,c)) t fex in
              if a1 then 
              hastype2 (Tclos(z,b1,c1)) t fex
              else (false,[],[]) 
            else (false,[],[]) 
      
          | Project ((i,n),x) -> raise NotImplemented
          | Let (d,x) -> (*let d1 = get_defined_v d [] in*)
          raise NotImplemented

          | FunctionCall(x,y) ->
            hastype2 (Tclos(e1,gt1,gut1)) t (FunctionCall(pmv,fex)) 
            
          | FunctionAbstraction(s,x) ->
            let gt11 = if exists_l gt1 s then removekeys gt1 [(s,0)] else gt1 in
            let(a,b,c)=hastype1 (Tclos(x,gt11,(s,Tclos(pmv,gt1,gut1))::gut1)) t in
            if a then (true,List.append (removekeys b [(s,0)]) gt1,c)
            else (false,[],[])
          | _ -> (false,[],[])
          end

        in
      hastype2 (Tclos(e1,gt,gut)) t pmv 
   
  | FunctionAbstraction(s,x) -> 
  begin 
    match t with Tfunc(t1,t2) ->
      let(a,b,c) = hastype1 (Tclos(x,(s,t1)::gt,gut)) t2 in 
      if a then 
        if exists_l gt s then 
          (true,(s,(extract_l gt s))::b,c)
        else (true,(removekeys b [(s,0)]),c) 
      else (false,[],[])
    | _-> (false,[],[])

  end
  end
      

let rec hastype g e t = 
  let (a,b,c) =  hastype1 (Tclos(e,g,[])) t in a
let rec yields g d g_dash = 
  let cl1 = exptoclosure g [] (get_defined_v d []) in
  let rec checktypeall cl1 g_dash = 
    match cl1 with [] -> true
    |(s1,cl1x)::cl1xs -> if exists_l g_dash s1 then 
    let (a,b,c) = hastype1 cl1x (extract_l g_dash s1) in 
    if a then checktypeall cl1xs g_dash else false
    else false
  in
  if checktypeall cl1 g_dash then
  let rec existsall l1 l2 =
    match l1 with [] -> true
    | (s1,l1x)::l1xs -> if exists_l l2 s1 then existsall l1xs l2 else false
  in
    existsall g_dash cl1
  else false
