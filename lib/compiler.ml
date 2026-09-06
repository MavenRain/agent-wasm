open Error

type artifact = { wasm : string; runtime : string; steps : int; arity : int }

let default_fuel = 1_000_000

let check ?(fuel = default_fuel) source =
  let budget = Budget.create fuel in
  let* parsed = Parser.parse budget source in
  let* checked = Kernel.check budget parsed in
  Ok (checked, budget)

let compile ?(fuel = default_fuel) source =
  let* checked, budget = check ~fuel source in
  let* runtime = Erase.run budget checked in
  let* wasm = Wasm.emit budget runtime in
  Ok { wasm; runtime = Erase.dump runtime; steps = Budget.used budget;
       arity = Kernel.arity checked }
