(** Runtime terms have no type, proof, or relevance constructor. *)
type term =
  | Local of int
  | Const of int64
  | Add of term * term
  | Fn of term
  | Call of term * term
  | Let of term * term

type t = private { body : term; arity : int }

val run : Budget.t -> Kernel.checked -> (t, Error.t) result
val dump : t -> string
