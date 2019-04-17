open A1
type krivineopcode =
  KADD | KMULT | KSUB | KEQ | KGE | KGT | KLT | KLE | KABS | KNOT | KNEG | KDIV | KREM  | KIFTE |KAND | KOR| CLOS of closure 

(* Function 'hastype' takes a set of type assumptions G represented as a list
of tuples of form (variable name, type), an expression and an expression
type, and returns if the expression has the claimed type under the given
assumptions. *)
val hastype : ((string * exptype) list) -> exptree -> exptype -> bool
val infertype:  ((string * exptype) list) -> exptree -> exptype
val infertype_closure: ((string * exptype) list) -> closure -> exptype
(* val infertype_answer: ((string * exptype) list) -> answer -> exptype *)

(* Function 'yields' takes a set of type assumptions G, a definition d and
another set of type assumptions G', and decides whether under the given
assumptions G, the definition d yields the type assumptions G' or not. *)
val yields: ((string * exptype) list) -> definition -> ((string * exptype) list) -> bool
val krivine_machine: closure -> (krivineopcode list) -> answer
val krivine_machine_in: closure -> (krivineopcode list) -> value
val secd_machine: answer list -> (string * answer) list -> opcode list -> (answer list * (string * answer) list * opcode list) list -> answer 