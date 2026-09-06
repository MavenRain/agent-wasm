(** Encode one pure u32 export as a core Wasm module, without external tools. *)
val emit : Budget.t -> Erase.t -> (string, Error.t) result
