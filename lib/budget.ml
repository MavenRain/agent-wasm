type t = { mutable remaining : int; initial : int }

let create n = { remaining = max 0 n; initial = max 0 n }
let used b = b.initial - b.remaining
let tick b =
  if b.remaining = 0 then Error Error.Budget_exhausted
  else (b.remaining <- b.remaining - 1; Ok ())
