(** A checked closed program with a Wasm-compatible public signature. *)
type checked

val check : Budget.t -> Ast.term -> (checked, Error.t) result
val term : checked -> Ast.term
val arity : checked -> int
