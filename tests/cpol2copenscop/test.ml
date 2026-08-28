open Printf 
open OpenScopReader
open OpenScopPrinter
open Pol2OpenScop
open PolPrinter
open CPolIRs

let run () = 
  cpol_printer "1_cpol.output" sample_cpol;
  let ocopenscop = CPolIRs.PolyLang.to_openscop sample_cpol in
  match ocopenscop with
  | Some copenscop -> 
    (openscop_printer "2_sample_copenscop.output" copenscop;
    (* This legacy smoke test checks both conversions complete.  It does not
       establish structural or semantic equality of the round trip. *)
    let ocpol' = CPolIRs.PolyLang.from_openscop sample_cpol copenscop in
    match ocpol' with
    | Okk cpol' -> cpol_printer "3_cpol.output" cpol'; printf "[legacy/cpol-openscop] PASS expected=both-conversions-succeed actual=both-conversions-succeeded interpretation=conversion-completed-without-claiming-structural-equality\n"
    | Err msg ->
        eprintf "[legacy/cpol-openscop] FAIL expected=OpenScop-to-Pol-success actual=conversion-rejection interpretation=%s\n" (Camlcoq.camlstring_of_coqstring msg);
        exit 1)
  | None -> 
      eprintf "[legacy/cpol-openscop] FAIL expected=Pol-to-OpenScop-success actual=conversion-rejection interpretation=no-OpenScop-value-produced\n";
      exit 1
;;

(** test both printer and reader *)
let () = 
  run ()
;;
