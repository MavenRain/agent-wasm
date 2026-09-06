(** Runtime terms have no type, proof, or relevance constructor. *)
type comparison = Equal | Less | Less_equal

type term =
  | Local of int
  | Const of int64
  | Add of term * term
  | Compare of comparison * term * term
  | If of term * term * term
  | Fn of term
  | Call of term * term
  | Let of term * term

type t = private { body : term; arity : int }

val run : Budget.t -> Kernel.checked -> (t, Error.t) result
val dump : t -> string
