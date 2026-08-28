(** test pluto works in ocaml *)
open Printf 
open Top
open PolPrinter
open Camlcoq
open CPolIRs


let () =
  let cpol_orig = CSample1.sample_cpol in
  cpol_printer "./orig.cpol" cpol_orig;
  match CPolIRs.scheduler cpol_orig with
  | Okk cpol_opt -> 
      cpol_printer "./opt.cpol" cpol_opt;
      printf "[legacy/pluto] PASS expected=scheduler-success actual=scheduler-success interpretation=Pluto-returned-a-convertible-schedule\n"
  | Err msg -> 
      eprintf "[legacy/pluto] FAIL expected=scheduler-success actual=scheduler-rejection interpretation=%s\n" (camlstring_of_coqstring msg);
      exit 1
;;
