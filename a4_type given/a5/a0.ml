(*2017cs10790 vishwajeet agrawal*)

(* Dummy implementation *)
type bigint = sign * int list
  and sign = Neg | NonNeg

(* helper functions*)
(*inverting a list*)


let invert l = let rec invert1 l1 l2 = match l1 with [] -> l2
                                | x::xs -> invert1 xs (x::l2) in invert1 l []
(*converting a positive integer into HLS list of digits*) (*HLS: head (of list) least significant, HMS: head most siginificant*)
let rec conv y = match y with
                | 0-> []
                | x -> (x mod 10) :: conv (x/10) 
(*add HLS lists of digits*)
let rec addi l1 l2 = let rec succ l = match l with
                                | []-> [1]
                                | x::xs -> if x<9 then (x+1)::xs
                                                else 0::(succ xs) in
						match l1 with
						| []-> l2
						|x::xs ->
							match l2 with
							| []->  (x::xs)
							| y::ys -> let z = x+y in
									if z<=9 then (z::(addi xs ys))
                               						else  ((z mod 10)::(succ (addi xs ys)))
(*add HMS list of digits*)
let addl l1 l2 = invert (addi (invert l1) (invert l2))
(*compare HMS *)
let comp l1 l2 = let rec compe l1 l2 = match l1 with []-> 0
                                     | x::xs -> match l2 with 
                                                | y::ys -> if x>y then 1 else if x<y then -1
                                                                else compe xs ys | []-> 1 in
		let s1 = List.length l1 in
		let s2 = List.length l2 in 
		if s1<s2 then -1
		else if s2<s1 then 1
		else compe l1 l2

exception NegativeNumber
exception IllFormedList
(*To get predecessor of a number represented as HLS*)
let rec pred l = match l with
                | x::xs -> if x>0 then 
                                match xs with []-> if x=1 then [] else [x-1]     
                                            | _-> (x-1)::xs
                           else ( match xs with
                                 y::ys-> (match ys with []-> if y=1 then [9] 
                                                                else  [9;y-1]
                                                 	|_->9::(pred (y::ys)) )
                                |[]-> raise IllFormedList )
                | []-> raise NegativeNumber 

exception IncorrectOrder

let rec concat l1 l2 = match l1 with []-> l2 | x::xs -> x::(concat xs l2)

let rec makezerolist n = if  n<=0 then [] else let l = makezerolist (n-1) in 0::l
(*To get predecessor of HLS and keeping 0's i.e. predz [0;0;1] = [9;9;0]*)
let rec predz l = let l1 = pred l in
                  let q= List.length l - List.length l1 in
                	concat l1 (makezerolist q)
(*Subtracting HLS and keeping leading zeros*)
let rec subi l1 l2 = match l2 with
                | []-> l1
                | y::ys -> (match l1 with
		                | x::xs -> if x>=y then (x-y)::(subi xs ys)
		                                else (10+x-y)::(subi (predz xs) ys)
		                | []-> raise IncorrectOrder )
(*removing leading zeros*)
let rec rmzeros l = match l with
                | []->[]
                | x::xs -> if x=0 then rmzeros xs else l
(*Subtracting HMS*)
let subl l1 l2 = rmzeros ( invert (subi (invert l1) (invert l2) ))
let subwithz l1 l2 = ( invert ( subi (invert l1) (invert l2) ) )
(*Comparing HMS but assuming MSD of l1 has same place as MSD of l2, e.g.. comphead [1;2;3] [2;1] = -1, [1;2;3] [1;2] =1, [1;2] [1;2] =0*)
let rec cmphead l1 l2 = match l2 with []-> (match l1 with []-> 0 | _-> 1)
                        | y::ys -> (match l1 with
                                        | x::xs -> if x>y then 1 else if x<y then -1 else cmphead xs ys
                                        | []-> -1)
(*getting l after removing first n digits*)
let rec taillist l n = match l with []->[]
                        | x::xs-> if n=0 then l else taillist xs (n-1)
(*getting first n digits of l*) 
let rec sublist l n = match l with []-> []
                		| x::xs-> if n=0 then [] else x::(sublist xs (n-1))

let mla a b c = let g = a*b+c in (g mod 10, g/10)

(*getting a*l+b, l as HLS e.g. smula 2 [1;3] 1 = 2*[1;3] +1 = [2;6] +1 = [3;6]*)
let rec smula a l b = match l with []-> if b=0 then [] else (b mod 10)::(smula a l (b/10) )
                        	| x::xs -> if a = 0 then (if b =0 then [] else (b mod 10)::(smula a l (b/10)  ))
                                        		else let (g,c) = mla a x b in
                                                		g::(smula a xs c)  
(*shifting l by x to the right, i.e. placing x zeros in front*)
let rec shiftr l x = if x=0 then l else
                        match l with [] -> []
                        |y::xs -> if x>0 then 0::(shiftr l (x-1) )
                                        else shiftr xs (x+1)
(*multiply HLS*)
let rec multli l1 l2 = match (l1,l2) with
                        | (x::xs,y::ys) -> addi (smula x l2 0) (shiftr (multli xs l2) 1)
                        | ([],_) -> []
                        | (_,[]) -> []
(*multiply HMS*)
let multl l1 l2 = invert ( multli ( invert l1) (invert l2) )

exception DivisionByZero


let eql l1 l2= if List.length l1 != List.length l2 then false
else
let rec listeq1 l1 l2 = if (l1=[] && l2=[]) then true
else (List.hd l1 = List.hd l2) && (listeq1 (taillist l1 1) (taillist l2 1)) in
listeq1 l1 l2

let geql l1 l2 = 
        if List.length l1 < List.length l2 then false
        else if List.length l1 > List.length l2 then true
        else let x = cmphead l1 l2 in if x = 0 || x = 1 then true else false


let rec divtl a b c =
        if eql b [] then raise DivisionByZero
        else
                let flg = geql a b in
                if not flg then c
        else divtl (subl a b) b (addl c [1])

(* This function is used to divide 2 integer lists and generate quotient such that remainder is positive *)
let divl a b = 
let rec divl1 a b t r = match a with
                        [] -> rmzeros r
                        |a::xs -> let vr = concat t [a] in
                                if not (geql vr b) then divl1 (xs) (b) (vr) (concat r [0])
                                else
                                        let k = divtl vr b [0] in
                                        let s = subl vr (multl b k) in
                                        divl1 (xs) (b) (s) (concat r k)
in 
divl1 a b [] []



let minus x = let (s,l) = x in
		match s with Neg -> (NonNeg,l)
			| NonNeg -> (Neg,l)
let abs x = let (s,l) = x in (NonNeg,l)

let add bg1 bg2 = let (s1,l1) = bg1 in let (s2,l2) = bg2 in
                  match (s1,s2) with
                | (NonNeg,NonNeg) -> (NonNeg, addl l1 l2)
                | (Neg,Neg) -> (Neg, addl l1 l2)
                | (NonNeg,Neg) -> let z = comp l1 l2 in
                                        if (z=0 || z=1)  then (NonNeg, subl l1 l2)
                                        else (Neg, subl l2 l1)
                | (Neg,NonNeg) -> let z = comp l2 l1 in
                                        if (z=0 || z=1) then (NonNeg, subl l2 l1)
                                        else (Neg, subl l1 l2)

let sub bg1 bg2 = let (s,l) = bg2 in let bg3 = match s with Neg -> (NonNeg,l)
                                                        | NonNeg -> (Neg,l) in
                        add bg1 bg3
let mult bg1 bg2 = let (s1,l1) = bg1 in let (s2, l2) = bg2 in
                        match (s1,s2) with
                        | (Neg,Neg) -> (NonNeg,multl l1 l2)
                        | (NonNeg,NonNeg) -> (NonNeg, multl l1 l2)
                        | (Neg, NonNeg) -> ( match l2  with []-> (NonNeg,[])
                                                          | _-> (Neg,multl l1 l2) )
                        | (NonNeg, Neg) -> ( match l1 with []-> (NonNeg,[])
                                                          | _ -> (Neg,multl l1 l2) )
                  


let div bg1 bg2 = let (s1,l1) = bg1 in let (s2,l2) = bg2 in let q = divl l1 l2 in if q=[] then (NonNeg,[]) else
                        match (s1,s2) with
                        | (NonNeg,NonNeg) -> (NonNeg, q)
                        | (NonNeg,Neg) ->  (Neg, q)
                        | (Neg,Neg) -> (NonNeg, q)
                        | (Neg, NonNeg) -> (Neg, q)
let rem a b =
        sub a (mult (div a b) b)
(* comparison functions*)
let eq x y = let (s1,l1) = x in let (s2,l2) = y in
		match (s1,s2) with (NonNeg,Neg)-> false
				| (Neg,NonNeg) -> false
				| _ -> let rec eql l1 l2 = ( match (l1,l2) with 
							| ([],[])-> true
							| ([],_)->false
							| (_,[])->false
							| (hl1::tl1,hl2::tl2)-> if (hl1=hl2) then eql tl1 tl2 
											else false ) 
					in eql l1 l2
let gt x y = let (s1,l1) = x in let (s2,l2) = y in
                match (s1,s2) with (NonNeg,Neg)-> true
                                | (Neg,NonNeg) -> false
				| (Neg,Neg) -> let s = comp l1 l2 in if s=(-1) then true else false 
				| (NonNeg, NonNeg) -> let s = comp l1 l2 in if s=1 then true else false
let geq x y = let (s1,l1) = x in let (s2,l2) = y in
                match (s1,s2) with (NonNeg,Neg)-> true
                                | (Neg,NonNeg) -> false
                                | (Neg,Neg) -> let s = comp l1 l2 in if s=1 then false else true
                                | (NonNeg, NonNeg) -> let s = comp l1 l2 in if s=(-1) then false else true
let lt x y = not (geq x y)
let leq x y = not (gt x y) 
 
let mk_big x = 
	match x with
	| 0 -> (NonNeg, [])
	| x -> if x > 0 then
			(NonNeg, invert (conv x))
	       else
			(Neg, invert (conv (-x)))

let print_num bg = let (s,l) = bg in if l=[] then "0" else 
                   let len = match s with Neg -> List.length l + 1
                                        | NonNeg -> List.length l in
                   let buf = Buffer.create len in
                   let charlist = let bigint2char bg = let rec int2charlist l = match l with []->[] |
                                                               			 x::xs -> char_of_int(x+48)::(int2charlist xs) in
                                                        let (s,lt) = bg in
                                                        match s with Neg-> char_of_int(45)::(int2charlist lt)
                                                       		| NonNeg -> int2charlist lt 
				  in bigint2char bg
                   in  List.iter (Buffer.add_char buf) charlist;
                   Buffer.contents buf



