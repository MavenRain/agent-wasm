type artifact = { wasm : string; runtime : string; steps : int; arity : int }

val default_fuel : int
val check : ?fuel:int -> string -> (Kernel.checked * Budget.t, Error.t) result
val compile : ?fuel:int -> string -> (artifact, Error.t) result
