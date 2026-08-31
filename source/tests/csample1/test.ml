open Printf 
open Top
open PolPrinter
open Camlcoq
open CPolIRs
open CPolOpt
open CSample1

let failed = ref false
let passed = ref 0

let check name res ok =
  if ok && res then begin
    passed := !passed + 1;
    printf "[legacy/csample1] PASS check=%s expected=ok:true,res:true actual=ok:%B,res:%B interpretation=refinement-established\n" name ok res
  end
  else begin
    failed := true;
    eprintf "[legacy/csample1] FAIL check=%s expected=ok:true,res:true actual=ok:%B,res:%B interpretation=refinement-not-established\n" name ok res
  end

let () =
  (* printf "Testing validation using pluto for csample1...\n"; *)
  let cpol_orig = CSample1.sample_cpol in
  cpol_printer "./orig.cpol" cpol_orig;
  (match CPolIRs.scheduler cpol_orig with
  | Okk cpol_opt -> 
      cpol_printer "./opt.cpol" cpol_opt;
      let (res, ok) = CPolOpt.validate cpol_orig cpol_opt in
      check "orig-to-opt" res ok;
      let (res, ok) = CPolOpt.validate cpol_opt cpol_orig  in
      check "opt-to-orig" res ok
  | Err msg -> 
      failed := true;
      eprintf "[legacy/csample1] FAIL check=scheduler expected=success actual=rejection interpretation=%s\n" (camlstring_of_coqstring msg));
  if !failed then exit 1
  else printf "[legacy/csample1] PASS expected=2 actual=%d interpretation=both-refinement-directions-established\n" !passed
;;
