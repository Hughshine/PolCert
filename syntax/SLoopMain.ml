open Diagnostics
open Result

let tool_name = "Syntax-Frontend Polyhedral Optimizer"

exception FrontendFailure of string

let frontend_failf fmt = Printf.ksprintf (fun s -> raise (FrontendFailure s)) fmt

let usage prog =
  Printf.sprintf
    "Usage: %s [--dump-input] [--dump-extracted-openscop] [--dump-scheduled-openscop] [--debug-scheduler] [--extract-only] <file.loop>"
    prog

type config = {
  mutable dump_input : bool;
  mutable dump_extracted_openscop : bool;
  mutable dump_scheduled_openscop : bool;
  mutable debug_scheduler : bool;
  mutable extract_only : bool;
  mutable input : string option;
}

let parse_args () =
  let cfg =
    {
      dump_input = false;
      dump_extracted_openscop = false;
      dump_scheduled_openscop = false;
      debug_scheduler = false;
      extract_only = false;
      input = None;
    }
  in
  let rec go i =
    if i >= Array.length Sys.argv then cfg
    else begin
      match Sys.argv.(i) with
      | "--dump-input" -> cfg.dump_input <- true; go (i + 1)
      | "--dump-extracted-openscop" -> cfg.dump_extracted_openscop <- true; go (i + 1)
      | "--dump-scheduled-openscop" -> cfg.dump_scheduled_openscop <- true; go (i + 1)
      | "--debug-scheduler" -> cfg.debug_scheduler <- true; go (i + 1)
      | "--extract-only" -> cfg.extract_only <- true; go (i + 1)
      | s when String.length s > 0 && s.[0] = '-' ->
          prerr_endline ("unknown option: " ^ s);
          prerr_endline (usage Sys.argv.(0));
          exit 2
      | file ->
          begin match cfg.input with
          | None -> cfg.input <- Some file; go (i + 1)
          | Some _ ->
              prerr_endline "only one input file is supported";
              prerr_endline (usage Sys.argv.(0));
              exit 2
          end
    end
  in
  go 1

let string_of_coq_err msg = Camlcoq.camlstring_of_coqstring msg

let print_section title body =
  print_endline ("== " ^ title ^ " ==");
  print_string body;
  if body = "" || body.[String.length body - 1] <> '\n' then print_newline ();
  print_newline ()

let rec nat_of_int n =
  if n <= 0 then Datatypes.O else Datatypes.S (nat_of_int (n - 1))

let rec int_of_nat = function
  | Datatypes.O -> 0
  | Datatypes.S n -> 1 + int_of_nat n

let string_of_z z = string_of_int (Camlcoq.Z.to_int z)

let string_of_aff (zs, c) =
  let coeffs = String.concat "," (List.map string_of_z zs) in
  Printf.sprintf "[%s | %s]" coeffs (string_of_z c)

let string_of_aff_list affs =
  "[" ^ String.concat "; " (List.map string_of_aff affs) ^ "]"

let string_of_access acc =
  let (arr, affs) = acc in
  Printf.sprintf "(%s,%s)" (string_of_int (Camlcoq.P.to_int arr)) (string_of_aff_list affs)

let string_of_access_list accs =
  "[" ^ String.concat "; " (List.map string_of_access accs) ^ "]"

let dump_poly_payload label pp =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let ((pis, varctxt), vars) = pp in
  Printf.eprintf
    "[debug] %s payload: pis=%d varctxt=%d vars=%d
"
    label (List.length pis) (List.length varctxt) (List.length vars);
  List.iteri
    (fun idx pi ->
      Printf.eprintf
        "[debug]   pi[%d]: depth=%d poly_rows=%d sched_rows=%d tf_rows=%d w=%d r=%d
"
        idx
        (int_of_nat (PL.pi_depth pi))
        (List.length (PL.pi_poly pi))
        (List.length (PL.pi_schedule pi))
        (List.length (PL.pi_transformation pi))
        (List.length (PL.pi_waccess pi))
        (List.length (PL.pi_raccess pi));
      Printf.eprintf
        "[debug]     schedule=%s
"
        (string_of_aff_list (PL.pi_schedule pi));
      Printf.eprintf
        "[debug]     transformation=%s
"
        (string_of_aff_list (PL.pi_transformation pi));
      Printf.eprintf
        "[debug]     waccess=%s
"
        (string_of_access_list (PL.pi_waccess pi));
      Printf.eprintf
        "[debug]     raccess=%s
"
        (string_of_access_list (PL.pi_raccess pi)))
    pis

let extract_poly loop =
  match SPolOpt.CoreOpt.Extractor.extractor loop with
  | Err msg -> frontend_failf "extractor failed: %s" (string_of_coq_err msg)
  | Okk pol -> pol

let poly_to_openscop pol =
  match SPolIRs.SPolIRs.PolyLang.to_openscop pol with
  | None -> frontend_failf "cannot convert extracted polyhedral model to OpenScop"
  | Some scop -> scop

let validate_components pp1 pp2 =
  let ((pil1, varctxt1), _) = pp1 in
  let ((pil2, _), _) = pp2 in
  let (wf1, wf1_ok) = SPolOpt.SVal.check_wf_polyprog pp1 in
  let (wf2, wf2_ok) = SPolOpt.SVal.check_wf_polyprog pp2 in
  let (eqdom, eqdom_ok) = SPolOpt.SVal.coq_EqDom pp1 pp2 in
  let env_dim = nat_of_int (List.length varctxt1) in
  let pil_ext = SPolIRs.SPolIRs.PolyLang.compose_pinstrs_ext pil1 pil2 in
  let valid_access = SPolOpt.SVal.check_valid_access pil_ext in
  let (res, res_ok) = SPolOpt.SVal.validate_instr_list (List.rev pil_ext) env_dim in
  ((wf1, wf1_ok), (wf2, wf2_ok), (eqdom, eqdom_ok), (valid_access, true), (res, res_ok))

let print_validate_components label pp1 pp2 =
  let ((wf1, wf1_ok), (wf2, wf2_ok), (eqdom, eqdom_ok), (valid_access, _), (res, res_ok)) =
    validate_components pp1 pp2
  in
  Printf.eprintf
    "[debug] %s components: wf1=%b(ok=%b) wf2=%b(ok=%b) eqdom=%b(ok=%b) valid_access=%b res=%b(ok=%b)\n"
    label wf1 wf1_ok wf2 wf2_ok eqdom eqdom_ok valid_access res res_ok

let extract_to_openscop loop =
  poly_to_openscop (extract_poly loop)

let schedule_poly pol =
  match SPolIRs.SPolIRs.scheduler pol with
  | Err msg -> frontend_failf "scheduler failed: %s" (string_of_coq_err msg)
  | Okk pol' -> pol'

let dump_scheduled_openscop loop =
  print_endline "== Scheduled OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (poly_to_openscop (schedule_poly (extract_poly loop)));
  print_newline ()

let debug_scheduler loop =
  let pol0 = extract_poly loop in
  dump_poly_payload "extracted" pol0;
  let pol = SPolOpt.PreparedOpt.Strengthen.strengthen_pprog pol0 in
  dump_poly_payload "strengthened" pol;
  let inscop = poly_to_openscop pol in
  let (self_valid, self_ok) = SPolOpt.SVal.validate pol pol in
  print_validate_components "validate(strengthened, strengthened)" pol pol;
  Printf.eprintf
    "[debug] validate(strengthened, strengthened) = %b (ok=%b, alarm=%b)\n"
    self_valid self_ok (not self_ok);
  let pol_roundtrip =
    match SPolIRs.SPolIRs.PolyLang.from_openscop_like_source pol inscop with
    | Okk pol' -> pol'
    | Err msg -> frontend_failf "self round-trip failed: %s" (string_of_coq_err msg)
  in
  let pol_complete_before =
    match SPolIRs.SPolIRs.PolyLang.from_openscop_complete inscop with
    | Okk pol' -> pol'
    | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
  in
  dump_poly_payload "roundtrip-before" pol_roundtrip;
  dump_poly_payload "complete-before" pol_complete_before;
  let (roundtrip_valid, roundtrip_ok) = SPolOpt.SVal.validate pol pol_roundtrip in
  print_validate_components "validate(strengthened, roundtrip-before)" pol pol_roundtrip;
  let (complete_before_valid, complete_before_ok) = SPolOpt.SVal.validate pol pol_complete_before in
  print_validate_components "validate(strengthened, complete-before)" pol pol_complete_before;
  print_endline "== Debug Extracted OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout inscop;
  print_newline ();
  print_endline "== Debug Roundtrip-Before OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (poly_to_openscop pol_roundtrip);
  print_newline ();
  Printf.eprintf
    "[debug] validate(strengthened, roundtrip-before) = %b (ok=%b, alarm=%b)\n"
    roundtrip_valid roundtrip_ok (not roundtrip_ok);
  let pol_sched = schedule_poly pol in
  dump_poly_payload "scheduled" pol_sched;
  let pol_complete_after =
    match SPolIRs.SPolIRs.scop_scheduler inscop with
    | Okk outscop ->
        begin match SPolIRs.SPolIRs.PolyLang.from_openscop_complete outscop with
        | Okk pol' -> pol'
        | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
        end
    | Err _ -> SPolIRs.SPolIRs.PolyLang.dummy
  in
  dump_poly_payload "complete-after" pol_complete_after;
  let (sched_valid, sched_ok) = SPolOpt.SVal.validate pol pol_sched in
  print_validate_components "validate(strengthened, scheduled)" pol pol_sched;
  let (complete_sched_valid, complete_sched_ok) = SPolOpt.SVal.validate pol_complete_before pol_complete_after in
  print_validate_components "validate(complete-before, complete-after)" pol_complete_before pol_complete_after;
  print_endline "== Debug Scheduled OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (poly_to_openscop pol_sched);
  print_newline ();
  Printf.eprintf
    "[debug] validate(strengthened, scheduled) = %b (ok=%b, alarm=%b)\n"
    sched_valid sched_ok (not sched_ok)

let dump_extracted_openscop loop =
  print_endline "== Extracted OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout (extract_to_openscop loop);
  print_newline ()

let () =
  try
    Gc.set { (Gc.get()) with
               Gc.minor_heap_size = 524288;
               Gc.major_heap_increment = 4194304 };
    let cfg = parse_args () in
    match cfg.input with
    | None ->
        print_endline (usage Sys.argv.(0));
        exit 2
    | Some file ->
        let prog = SLoopParse.parse_file file in
        let loop = SLoopElab.elaborate prog in
        if cfg.dump_input then print_section "Input Loop" (SLoopPretty.string_of_loop loop);
        if cfg.extract_only then begin
          OpenScopPrinter.openscop_printer' stdout (extract_to_openscop loop);
          print_newline ();
          exit 0
        end;
        if cfg.dump_extracted_openscop then dump_extracted_openscop loop;
        if cfg.dump_scheduled_openscop then dump_scheduled_openscop loop;
        if cfg.debug_scheduler then debug_scheduler loop;
        let (optimized, ok) =
          SPolOpt.opt loop
        in
        if not ok then prerr_endline "[alarm] optimization triggered a checked fallback or warning";
        print_section "Optimized Loop" (SLoopPretty.string_of_loop optimized)
  with
  | Sys_error msg -> error no_loc "%s" msg; exit 2
  | SLoopParse.Error (pos, msg) -> error no_loc "parse error at byte %d: %s" pos msg; exit 2
  | SLoopElab.Error msg -> error no_loc "elaboration error: %s" msg; exit 2
  | FrontendFailure msg -> error no_loc "%s" msg; exit 2
  | CertcheckerConfig.CertCheckerFailure (_, msg) ->
      error no_loc "optimization failed inside extracted runtime: %s" msg; exit 2
  | e -> crash e
