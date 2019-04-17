open A1
exception InvalidExptree
exception InvalidDefinition
exception Insufficient_TA

let rec extract_l st_e st = match st_e with [] -> raise Insufficient_TA
            | ((a,b))::xs -> 
            if compare st a = 0 then b
            else extract_l xs st
let rec exists_l st_e st = match st_e with [] -> false
            | ((a,b))::xs -> 
            if compare st a = 0 then true
            else exists_l xs st 


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
  if t = infertype g e then true else false
  with InvalidExptree | InvalidDefinition -> false

let yields g d g_dash = 
  let tl1 = definedvar_type g d in
  let dx1 = eliminate_dups tl1 [] in
    checkcontains dx1 g_dash && checkcontains g_dash dx1
  