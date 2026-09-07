type t =
  | Parse of string
  | Unknown_name of string
  | Empty_record
  | Duplicate_field of string
  | Unknown_field of string
  | Invalid_index of int
  | Invalid_u32 of int64
  | Type_mismatch
  | Expected_function
  | Erased_use of int
  | Runtime_proof
  | Unsupported_export
  | Budget_exhausted
  | Backend of string
  | Io of string

let message = function
  | Parse s -> "parse: " ^ s
  | Unknown_name s -> "unknown name: " ^ s
  | Empty_record -> "record must contain at least one field"
  | Duplicate_field s -> "duplicate record field: " ^ s
  | Unknown_field s -> "unknown record field: " ^ s
  | Invalid_index n -> "invalid variable index: " ^ string_of_int n
  | Invalid_u32 n -> "outside u32 range: " ^ Int64.to_string n
  | Type_mismatch -> "type mismatch (including equality endpoints or relevance)"
  | Expected_function -> "expected a function"
  | Erased_use n -> "erased variable used at runtime: index " ^ string_of_int n
  | Runtime_proof -> "equality evidence may only occur in erased positions"
  | Unsupported_export -> "export must have type u32 -> ... -> u32 with runtime parameters"
  | Budget_exhausted -> "compiler work budget exhausted; simplify or split the program"
  | Backend s -> "backend: " ^ s
  | Io s -> "I/O: " ^ s

let ( let* ) = Result.bind
