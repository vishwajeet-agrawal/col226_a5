open A1
exception Not_implemented
exception Insufficient_TA
exception InvalidExptree
(* exception Undecidable *)
exception InvalidDefinition
type tclosure = 
  Tclos of exptree * (string * exptype list) * (string * closure  list)
 
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

(* given type hastype checks if big step reduction of a closure is that type *)
(* given a type list yields checks if big step reduction of a  closure list is that type list *)
(* closure is basically a type closure *)


(* string exptree bool exptype *)
(* bvls_exists bvls_get_exp bvls_check_allowed bvls_get_type bvls_get_tuple *)
(* hastype returns bool*bvls *)
(* string*exptree string*exp *)

let rec hastype g e t = 
  let rec hasoneoftuple g e t i n =
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
    in
  match e with 
  | Var (x) -> (extract_l g x)=t 
  | N ( x) -> Tint=t
  | Sub (a,b) (*->  t=Tint && hastype g a && hastype g b*) (*if t=Tint then (let x = hastype g a Tint in*) 
                                  (* let y = hastype g b Tint in *)
                                  (* if x && y then true else raise InvalidExptree) else false *)
  | Add  (a,b) (*-> t=Tint && hastype g a && hastype g b*) (*if t=Tint then (let x = hastype g a Tint in*) 
                                  (* let y = hastype g b Tint in *)
                                  (* if x && y then true else raise InvalidExptree) else false *)
  | Rem   (a,b) (*-> t=Tint && hastype g a && hastype g b*) (*if t=Tint then (let x = hastype g a Tint in*) 
                                  (* let y = hastype g b Tint in *)
                                  (* if x && y then true else raise InvalidExptree) else false *)
  | Div   (a,b) (*-> t=Tint && hastype g a && hastype g b*) (*if t=Tint then (let x = hastype g a Tint in*) 
                                  (* let y = hastype g b Tint in *)
                                  (* if x && y then true else raise InvalidExptree) else false *)
  | Mult  (a,b) -> t=Tint && hastype g a Tint && hastype g b Tint (*if t=Tint then (let x = hastype g a Tint in*) 
                                  (* let y = hastype g b Tint in *)
                                  (* if x && y then true else raise InvalidExptree) else false  *)
  | Abs   a     ->  t=Tint && hastype g a Tint (*if t=Tint then (if hastype g a Tint then true else false*)(*raise InvalidExptree else false*)
  | Negative   a     -> t=Tint && hastype g a Tint(*if t=Tint then (if hastype g a Tint then true else false*)(*raise InvalidExptree else false*)
  | B ( x) -> t=Tbool
  | Not ( x) -> if t=Tbool then (if hastype g x Tbool then true else false(*raise InvalidExptree*)) else false
  | Conjunction (x, y) -> if t=Tbool then (if hastype g x Tbool && hastype g y Tbool then true else false(*raise InvalidExptree*)) else false
  | Disjunction (x,y)  -> if t=Tbool then (if hastype g x Tbool && hastype g y Tbool then true else false(*raise InvalidExptree*)) else false
  | Equals (x,y) ->  if t=Tbool then (if (hastype g x Tbool && hastype g y Tbool) || (hastype g x Tint && hastype g y Tint) then true else false(*raise InvalidExptree*)) else false
  | GreaterTE (x,y) -> if t=Tbool then (if hastype g x Tint && hastype g y Tint then true else false(*raise InvalidExptree*)) else false
  | LessTE (x,y) -> if t=Tbool then (if hastype g x Tint && hastype g y Tint then true else false(*raise InvalidExptree*)) else false
  | GreaterT (x,y) -> if t=Tbool then (if hastype g x Tint && hastype g y Tint then true else false(*raise InvalidExptree*)) else false
  | LessT (x,y) -> if t=Tbool then (if hastype g x Tint && hastype g y Tint then true else false(*raise InvalidExptree*)) else false
  | InParen (x) -> hastype g x t
  | IfThenElse (x,y,z) -> if ( hastype g x Tbool) then let a=hastype g y t in let b = hastype g z t in if (a=b) then a else false(*raise InvalidExptree*)  else false(*raise InvalidExptree*) 
  | Tuple (x,y) -> 
              if x = (List.length y) then begin
              match t with  Ttuple (typel) ->
                      if List.length typel = x then
                        let rec checkt ta ya =
                          match (ta,ya) with ([],[]) -> true
                          | (tax::taxs,yax::yaxs) -> if hastype g yax tax then 
                                                          checkt taxs yaxs
                                                    else false 
                          | _-> false in
                          checkt typel y
                      else false
                  | _ -> false end             
                  else false(*raise InvalidExptree*)
  | Project ((x,y),z) ->   if (x>0 && x<=y) then
                                              
                                                  (* begin match z with Tuple (a,b) -> if a=y then 
                                                                              hastype g (List.nth b (x-1)) t
                                                                              else  false(*raise InvalidExptree*)
                                                        | Var (a) -> extract_l g a = t
                                                        
                                                        end
                                                        | _ -> false(*raise InvalidExptree*) *)
                                                        hasoneoftuple g z t x y
                                                  (* end *)
                            else  false(*raise InvalidExptree*)
  | Let (d,ee) -> let def_v = get_defined_v d [] in
                  hastype g (substitute_lx ee def_v []) t
                  
  | FunctionAbstraction (s,ee) -> begin match t with Tfunc (t1,t2) ->
                                                  hastype ((s,t1)::g) ee t2
                                                | _-> false end
  | FunctionCall (e1,e2) -> begin
        match e1 with FunctionAbstraction (s,ee) ->
        hastype g (substitute_lx ee [(s,e2)] []) t
        | InParen(e3) -> hastype g (FunctionCall(e3,e2)) t
        | Let(d,e3) -> let def_v = get_defined_v d [] in
            
        | Project ((i,n),e3) ->
        | IfThenElse (x,y,z) -> if hastype g x Tbool then 
          hastype g (FunctionCall(y,e2)) t && hastype g (FunctionCall(z,e2)) t else false
        | FunctionCall(e3,e4) ->
        |_ -> false(*raise InvalidExptree*)
    end


  (* yields : ((string * exptype) list) -> definition -> ((string * exptype) list) -> bool *)

let rec yields g d g_dash = 
  let dl1 = get_defined_v d g in
  let rec checktype g dl g_dash =
    match dl with [] ->[]
    |(s,e)::dlxs -> (hastype g e (extract_l g_dash s)) && checktype g dlxs g_dash in
  let rec check_allkeys d1 d2 = 
    match d1 with [] -> true 
    | (s,e)::d1xs -> let p x = (let (s1,v1) = x in s1=s) in if List.exists p d2  then check_allkeys d1xs d2 else false in
  check_allkeys g_dash d && checktype g d g_dash

  (* let rec checkequality dl1 dl2 = 
  match dl1 with [] -> true
       | dl1x::dlxs -> let p x = x = dl1x in if (List.exists p dl2) then (checkequality dlxs dl2) else false 
    in checkequality dl1 g_dash && checkequality g_dash dl1 *)

(* gives defined variables plus the new list *)


(* correct *)

(* Y1[Y2] *)
(* let def_aug d1 d2 =
let rec def_augment d1 d2 d3=  *)
  (* match d1 with [] -> List.rev_append d2 d3
  | (x,e)::xs -> 
  let rec check_disjoint1 x d2t=
    match d2t with [] -> true
      | (y,e2)::ys -> if x=y then false else check_disjoint1 x ys 
    in
    if check_disjoint1 x d2 then def_augment xs d2 ((x,e)::d3)
    else def_augment xs d2 d3
    in def_augment d1 d2 [] *)

(* defined variables is a list (stack) in 
  which the the value of any variable is the value of the first 
  occurence of that variable in the list *)
(* union of two dv(1) U dv(2) if intersection is null same as check intersect then augment*)
(* augmentation dv1[dv2] *)
(* check for intersection *)
(* same for used variables *)
(* let augment_dv d1 d2 = List.append d2 d1  *)


(* let rec substitute_x f x e=
  match f with 
  Var a  ->  if x=a then e else f  (* variables starting with a Capital letter, represented as alphanumeric strings with underscores (_) and apostrophes (') *)
  | N a ->  f     (* Integer constant *)
  | B a -> f    (* Boolean constant *)
  (* unary operators on integers *)
  | Abs a -> Abs (substitute_x a x e)                   (* abs *)
  | Negative a -> Negative (substitute_x a x e)              (* unary minus ~ *)
  (* unary operators on booleans *)
  | Not a -> Not (substitute_x a x e)
  (* binary operators on integers *)
  | Add (a,b) -> Add (substitute_x a x e,substitute_x b x e)         (* Addition + *)
  | Sub (a,b) -> Sub (substitute_x a x e,substitute_x b x e)      (* Subtraction - *)
  | Mult (a,b) -> Mult (substitute_x a x e,substitute_x b x e)       (* Multiplication * *)
  | Div (a,b) -> Div (substitute_x a x e,substitute_x b x e)         (* div *)
  | Rem (a,b) -> Rem (substitute_x a x e,substitute_x b x e)        (* mod *)
  (* binary operators on booleans *)
  | Conjunction (a,b) -> Conjunction (substitute_x a x e,substitute_x b x e) (* conjunction /\ *)
  | Disjunction (a,b) -> Disjunction (substitute_x a x e,substitute_x b x e) (* binary operators on booleans \/ *)
  (* comparison operations on integers *)
  | Equals (a,b) -> Equals (substitute_x a x e,substitute_x b x e)      (* = *)
  | GreaterTE (a,b) -> GreaterTE (substitute_x a x e,substitute_x b x e)   (* >= *)
  | LessTE (a,b) -> LessTE (substitute_x a x e,substitute_x b x e)      (* <= *)
  | GreaterT (a,b) -> GreaterT (substitute_x a x e,substitute_x b x e)    (* > *)
  | LessT (a,b) -> LessT (substitute_x a x e,substitute_x b x e)       (* < *)
  (* expressions using parenthesis *)
  | InParen a -> InParen (substitute_x a x e)               (* ( ) *)
  (* a conditional expression *)
  | IfThenElse (a,b,c) -> IfThenElse (substitute_x a x e,substitute_x b x e,substitute_x c x e)  (* if then else fi  *)
  (* creating n-tuples (n >= 0) *)
  | Tuple (a,b) -> let sub_xe a = substitute_x a x e in Tuple (a,List.map sub_xe b)
  (* projecting the i-th component of an expression (which evaluates to an n-tuple, and 1 <= i <= n) *)
  | Project ((a,b),c) -> Project ((a,b),substitute_x c x e)   (* Proj((i,n), e)  0 < i <= n *)
  | Let (a,b) -> let vbls1 = get_defined_v a [] in 
              let p1 a = let (vr1,ex1) = a in vr1=x in
              if List.exists p1 vbls1 then 
                Let (a,b)
              else Let(a,subsitute_x b x e)
  | FunctionAbstraction (a,b) -> if a = x then FunctionAbstraction(a,b) else FunctionAbstraction(a,substitute_x b x e)
  | FunctionCall (a,b) -> FunctionCall (substitute_x a x e,substitute_x b x e) *)

(* x are bound variables lx are free variables that need to be substituted *)


(* function to get defined variables returns a table that *)
(* let subs_d xd1 ld1 = 
let rec subs xd ld ld2= 
  let (s,e) = xd in
  match ld with [] -> xd::ld2
  | (x,e1)::xs -> if x = s then List.rev_append ld2 ((x,e)::xs) else subs xd xs ((x,e1)::ld2) 
in subs xd1 ld1 [] *)