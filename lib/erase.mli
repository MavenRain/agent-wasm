(** Runtime terms have no type, proof, or relevance constructor. *)
type comparison = Equal | Less | Less_equal

type term =
  | Local of int
  | Const of int64
  | Add of term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | Record of (string * term) list
  | Field of term * string
  | Compare of comparison * term * term
  | If of term * term * term
  | Fn of term
  | Call of term * term
  | Let of term * term

type t = private { body : term; arity : int }

(** Build a runtime program directly, without a kernel derivation. Backend
    clients and tests use this to reach emission arms that no source program
    can produce. Emission rejects invalid local indices, out-of-range u32
    constants, and negative arity with explicit errors. *)
val program : int -> term -> t

val run : Budget.t -> Kernel.checked -> (t, Error.t) result
val dump : t -> string
