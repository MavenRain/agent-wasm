open Agent_wasm
open Error

(* The standard library reports filesystem failures as exceptions. Translate
   them to typed errors at the CLI boundary; compiler modules use Result. *)
let io action = try Ok (action ()) with Sys_error message -> Error (Io message)

let read path = io (fun () -> In_channel.with_open_bin path In_channel.input_all)
let write path bytes = io (fun () ->
  Out_channel.with_open_bin path (fun output -> Out_channel.output_string output bytes))

let file_identity path =
  try
    let stat = Unix.stat path in
    Ok (Some (stat.Unix.st_dev, stat.Unix.st_ino))
  with
  | Unix.Unix_error (Unix.ENOENT, _, _) -> Ok None
  | Unix.Unix_error (code, operation, argument) ->
      Error (Io (operation ^ " " ^ argument ^ ": " ^ Unix.error_message code))

let distinct_files source output =
  let* source_id = file_identity source in
  let* output_id = file_identity output in
  let same = Option.bind source_id (fun s -> Option.map (( = ) s) output_id) in
  if source = output || Option.value same ~default:false
  then Error (Io "source and output must be different files")
  else Ok ()

let usage = "usage: agent-wasm [--fuel N] check SOURCE | compile SOURCE OUTPUT.wasm | ir SOURCE"

let dispatch fuel = function
  | ["check"; path] ->
      let* source = read path in
      let* checked, budget = Compiler.check ~fuel source in
      Printf.printf "checked: %d parameter(s), %d steps\n" (Kernel.arity checked) (Budget.used budget);
      Ok ()
  | ["compile"; path; output] ->
      let* () = distinct_files path output in
      let* source = read path in
      let* artifact = Compiler.compile ~fuel source in
      let* () = write output artifact.wasm in
      Printf.printf "compiled: %d bytes, %d steps\n" (String.length artifact.wasm) artifact.steps;
      Ok ()
  | ["ir"; path] ->
      let* source = read path in
      let* checked, budget = Compiler.check ~fuel source in
      let* runtime = Erase.run budget checked in
      print_string (Erase.dump runtime);
      Ok ()
  | [] | _ :: _ -> Error (Parse usage)

let run = function
  | "--fuel" :: amount :: rest ->
      let* fuel = Option.to_result ~none:(Parse "fuel must be an integer") (int_of_string_opt amount) in
      if fuel <= 0 then Error (Parse "fuel must be positive") else dispatch fuel rest
  | ([] | _ :: _) as rest -> dispatch Compiler.default_fuel rest

let () =
  let arguments = match Array.to_list Sys.argv with [] -> [] | _program :: rest -> rest in
  Result.fold ~ok:(fun () -> ()) ~error:(fun e -> prerr_endline (Error.message e); exit 1) (run arguments)
