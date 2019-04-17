open A1
open A4
val closure_table: (string * closure) list ref
val closure_type_table: (string * exptype) list ref
val environment: (string * answer) list ref
val environment_type: (string * exptype) list ref
(* val stack: answer list ref *)
(* val dump: (answer list * (string * answer) list * opcode list) list ref *)
val make_closure: string -> bool -> closure
val execute_secd: string -> answer
val execute_krivine: string -> answer
val add_closure: string -> closure -> unit
val add_closure_type: string -> string -> unit
val add_answer_type: string -> string -> unit 
val add_answer: string -> string -> answer -> unit
val make_recursive_closure: string -> string -> bool -> closure
val add_recursive_closure: string -> closure -> unit

val exp_parser: string -> exptree
val type_parser: string -> exptype
