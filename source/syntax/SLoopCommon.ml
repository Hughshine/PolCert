exception FrontendFailure of string

let frontend_failf fmt = Printf.ksprintf (fun s -> raise (FrontendFailure s)) fmt

let string_of_coq_err msg = Camlcoq.camlstring_of_coqstring msg

let rec nat_of_int n =
  if n <= 0 then Datatypes.O else Datatypes.S (nat_of_int (n - 1))

let rec int_of_nat = function
  | Datatypes.O -> 0
  | Datatypes.S n -> 1 + int_of_nat n
