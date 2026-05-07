open Diagnostics
open Result
open SLoopCommon
open SLoopCli
open SLoopDispatch
open SLoopProfile

let tool_name = "Syntax-Frontend Polyhedral Optimizer"

module ParallelValidatorCore = Validator.Validator(SPolIRs.SPolIRs)
module ParallelCodegenCore = ParallelCodegen.ParallelCodegen(SPolIRs.SPolIRs)
module ParallelLoopIR = ParallelCodegenCore.ParallelLoop
module ParallelBaseLoop = ParallelLoopIR.BaseLoop
module ParallelInstr = SPolIRs.SPolIRs.Instr

let pluto_tiling_mode second_level =
  if second_level
  then PlutoTilingValidator.SecondLevel
  else PlutoTilingValidator.Ordinary

let diamond_midpoint_label full =
  if full then "mid_full_diamond" else "mid_diamond"

let usage = SLoopCli.usage
let parse_args = SLoopCli.parse_args
let validate_flag_model = SLoopCli.validate_flag_model
let configure_scheduler_modes = SLoopCli.configure_scheduler_modes

let read_openscop_or_fail path =
  match OpenScopReader.read path with
  | Some scop -> scop
  | None -> frontend_failf "cannot read OpenScop file %s" path

let print_section title body =
  print_endline ("== " ^ title ^ " ==");
  print_string body;
  if body = "" || body.[String.length body - 1] <> '\n' then print_newline ();
  print_newline ()

let max_int a b = if a >= b then a else b

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

let nth_or xs n default =
  try List.nth xs n with _ -> default

let name_of_ident id = Camlcoq.extern_atom id
let name_of_nat n = string_of_int (Camlcoq.Nat.to_int n)

let rec string_of_parallel_loop_expr_raw env = function
  | ParallelBaseLoop.Constant z -> string_of_z z
  | ParallelBaseLoop.Var n -> nth_or env (Camlcoq.Nat.to_int n) ("v" ^ name_of_nat n)
  | ParallelBaseLoop.Sum (a, b) ->
      Printf.sprintf "(%s + %s)"
        (string_of_parallel_loop_expr_raw env a)
        (string_of_parallel_loop_expr_raw env b)
  | ParallelBaseLoop.Mult (k, e) ->
      Printf.sprintf "(%s * %s)" (string_of_z k) (string_of_parallel_loop_expr_raw env e)
  | ParallelBaseLoop.Div (e, k) ->
      Printf.sprintf "(%s / %s)" (string_of_parallel_loop_expr_raw env e) (string_of_z k)
  | ParallelBaseLoop.Mod (e, k) ->
      Printf.sprintf "(%s %% %s)" (string_of_parallel_loop_expr_raw env e) (string_of_z k)
  | ParallelBaseLoop.Max (a, b) ->
      Printf.sprintf "max(%s, %s)"
        (string_of_parallel_loop_expr_raw env a)
        (string_of_parallel_loop_expr_raw env b)
  | ParallelBaseLoop.Min (a, b) ->
      Printf.sprintf "min(%s, %s)"
        (string_of_parallel_loop_expr_raw env a)
        (string_of_parallel_loop_expr_raw env b)

let string_of_parallel_loop_expr env e =
  string_of_parallel_loop_expr_raw env e

let parallel_slot_expr slots n =
  nth_or slots (Camlcoq.Nat.to_int n) (ParallelBaseLoop.Constant (Camlcoq.Z.of_sint 0))

let string_of_parallel_affine env slots aff =
  let rec go = function
    | ParallelInstr.AeConst z -> string_of_z z
    | ParallelInstr.AeVar n -> string_of_parallel_loop_expr env (parallel_slot_expr slots n)
    | ParallelInstr.AeAdd (a, b) -> Printf.sprintf "(%s + %s)" (go a) (go b)
    | ParallelInstr.AeSub (a, b) -> Printf.sprintf "(%s - %s)" (go a) (go b)
    | ParallelInstr.AeMul (k, e) ->
        if Camlcoq.Z.eq k Camlcoq.Z.zero then "0"
        else if Camlcoq.Z.eq k Camlcoq.Z.one then go e
        else Printf.sprintf "(%s * %s)" (string_of_z k) (go e)
  in
  go aff

let string_of_parallel_access env slots = function
  | ParallelInstr.AcVar id -> name_of_ident id
  | ParallelInstr.AcArr (id, idxs) ->
      let base = name_of_ident id in
      List.fold_left
        (fun acc idx -> acc ^ "[" ^ string_of_parallel_affine env slots idx ^ "]")
        base idxs

let string_of_parallel_instr_expr env slots expr =
  let rec go = function
    | ParallelInstr.ExConst z -> string_of_z z
    | ParallelInstr.ExFloat lit -> Camlcoq.camlstring_of_coqstring lit
    | ParallelInstr.ExVar n -> string_of_parallel_loop_expr env (parallel_slot_expr slots n)
    | ParallelInstr.ExAccess a -> string_of_parallel_access env slots a
    | ParallelInstr.ExAdd (a, b) -> Printf.sprintf "(%s + %s)" (go a) (go b)
    | ParallelInstr.ExSub (a, b) -> Printf.sprintf "(%s - %s)" (go a) (go b)
    | ParallelInstr.ExMul (a, b) -> Printf.sprintf "(%s * %s)" (go a) (go b)
    | ParallelInstr.ExDiv (a, b) -> Printf.sprintf "(%s / %s)" (go a) (go b)
    | ParallelInstr.ExLe (a, b) -> Printf.sprintf "(%s <= %s)" (go a) (go b)
    | ParallelInstr.ExEq (a, b) -> Printf.sprintf "(%s == %s)" (go a) (go b)
    | ParallelInstr.ExAnd (a, b) -> Printf.sprintf "(%s && %s)" (go a) (go b)
    | ParallelInstr.ExCall (fn, args) ->
        let fn = Camlcoq.camlstring_of_coqstring fn in
        let args =
          match List.map go args with
          | [] -> ""
          | hd :: tl -> List.fold_left (fun acc s -> acc ^ ", " ^ s) hd tl
        in
        Printf.sprintf "%s(%s)" fn args
    | ParallelInstr.ExCond (c, t, f) ->
        Printf.sprintf "(%s ? %s : %s)" (go c) (go t) (go f)
  in
  go expr

let string_of_parallel_test env tst =
  let rec go = function
    | ParallelBaseLoop.LE (a, b) ->
        Printf.sprintf "%s <= %s"
          (string_of_parallel_loop_expr env a)
          (string_of_parallel_loop_expr env b)
    | ParallelBaseLoop.EQ (a, b) ->
        Printf.sprintf "%s == %s"
          (string_of_parallel_loop_expr env a)
          (string_of_parallel_loop_expr env b)
    | ParallelBaseLoop.And (a, b) -> Printf.sprintf "(%s && %s)" (go a) (go b)
    | ParallelBaseLoop.Or (a, b) -> Printf.sprintf "(%s || %s)" (go a) (go b)
    | ParallelBaseLoop.Not t -> Printf.sprintf "!(%s)" (go t)
    | ParallelBaseLoop.TConstantTest true -> "true"
    | ParallelBaseLoop.TConstantTest false -> "false"
  in
  go tst

let rec parallel_stmt_list_to_list = function
  | ParallelLoopIR.SNil -> []
  | ParallelLoopIR.SCons (st, tl) -> st :: parallel_stmt_list_to_list tl

let parallel_indent n = String.make (2 * n) ' '

let fresh_parallel_loop_name env depth =
  let rec pick n =
    let cand = Printf.sprintf "i%d" (depth + n) in
    if List.mem cand env then pick (n + 1) else cand
  in
  pick 0

let rec lines_of_parallel_stmt env depth lvl = function
  | ParallelLoopIR.Loop (mode, _, lb, ub, body) ->
      let v = fresh_parallel_loop_name env depth in
      let loop_kw =
        match mode with
        | ParallelLoopIR.SeqMode -> "for"
        | ParallelLoopIR.ParMode -> "parallel for"
        | ParallelLoopIR.VecMode -> "vector for"
      in
      let header =
        Printf.sprintf "%s%s %s in range(%s, %s) {"
          (parallel_indent lvl)
          loop_kw
          v
          (string_of_parallel_loop_expr env lb)
          (string_of_parallel_loop_expr env ub)
      in
      let body_lines = lines_of_parallel_stmt (v :: env) (depth + 1) (lvl + 1) body in
      header :: body_lines @ [parallel_indent lvl ^ "}"]
  | ParallelLoopIR.Instr (instr, slots) ->
      begin match instr with
      | ParallelInstr.SSkip -> [parallel_indent lvl ^ "skip;"]
      | ParallelInstr.SAssign (lhs, rhs) ->
          [parallel_indent lvl
           ^ string_of_parallel_access env slots lhs
           ^ " = "
           ^ string_of_parallel_instr_expr env slots rhs
           ^ ";"]
      end
  | ParallelLoopIR.Seq stmts ->
      List.concat (List.map (lines_of_parallel_stmt env depth lvl) (parallel_stmt_list_to_list stmts))
  | ParallelLoopIR.Guard (tst, body) ->
      let header =
        Printf.sprintf "%sif (%s) {" (parallel_indent lvl) (string_of_parallel_test env tst)
      in
      let body_lines = lines_of_parallel_stmt env depth (lvl + 1) body in
      header :: body_lines @ [parallel_indent lvl ^ "}"]

let string_of_parallel_loop (((stmt, varctxt), _vars) : ParallelLoopIR.t) =
  let ctxt_names = List.map name_of_ident varctxt in
  let header =
    match ctxt_names with
    | [] -> []
    | _ -> ["context(" ^ String.concat ", " ctxt_names ^ ");"; ""]
  in
  String.concat "\n" (header @ lines_of_parallel_stmt (List.rev ctxt_names) 0 0 stmt) ^ "\n"

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

let debug_env_enabled name =
  match Sys.getenv_opt name with
  | Some ("1" | "true" | "TRUE" | "yes" | "YES") -> true
  | _ -> false

let dump_poly_payload_if name label pp =
  if debug_env_enabled name then dump_poly_payload label pp

let dump_bandaffine_payload label env_size pil_ext =
  let module BA = STilingBandSched.CoreBandSched.BandAffine in
  Printf.eprintf
    "[debug] %s band-payload: env=%d pis=%d\n"
    label env_size (List.length pil_ext);
  List.iteri
    (fun idx pi ->
      Printf.eprintf
        "[debug]   ext[%d]: depth=%d sched1=%s sched2=%s tf=%s w=%s r=%s\n"
        idx
        (int_of_nat (BA.PolyLang.pi_depth_ext pi))
        (string_of_aff_list (BA.PolyLang.pi_schedule1_ext pi))
        (string_of_aff_list (BA.PolyLang.pi_schedule2_ext pi))
        (string_of_aff_list (BA.PolyLang.pi_transformation_ext pi))
        (string_of_access_list (BA.PolyLang.pi_waccess_ext pi))
        (string_of_access_list (BA.PolyLang.pi_raccess_ext pi)))
    pil_ext

let debug_bandaffine_pair_checks label env_size pil_ext =
  let module BA = STilingBandSched.CoreBandSched.BandAffine in
  let valid_access = BA.check_valid_access pil_ext in
  Printf.eprintf
    "[debug] %s valid_access=%b env=%d\n"
    label valid_access (int_of_nat env_size);
  let rec debug_self i = function
    | [] -> ()
    | pi :: rest ->
        let (res, ok) = BA.validate_two_instrs pi pi env_size in
        Printf.eprintf
          "[debug] %s self[%d]=%b(ok=%b)\n"
          label i res ok;
        debug_self (i + 1) rest
  in
  let rec debug_pairs i = function
    | [] -> ()
    | pi :: rest ->
        let rec debug_with j = function
          | [] -> ()
          | pj :: rest' ->
              let (fwd, ok_fwd) = BA.validate_two_instrs pi pj env_size in
              let (rev, ok_rev) = BA.validate_two_instrs pj pi env_size in
              Printf.eprintf
                "[debug] %s pair[%d,%d] fwd=%b(ok=%b) rev=%b(ok=%b)\n"
                label i j fwd ok_fwd rev ok_rev;
              debug_with (j + 1) rest'
        in
        debug_with (i + 1) rest;
        debug_pairs (i + 1) rest
  in
  debug_self 0 pil_ext;
  debug_pairs 0 pil_ext

let extract_poly loop =
  match SPolOpt.CoreOpt.Extractor.extractor loop with
  | Err msg -> frontend_failf "extractor failed: %s" (string_of_coq_err msg)
  | Okk pol -> pol

let poly_to_openscop pol =
  match SPolOpt.to_source_openscop pol with
  | None -> frontend_failf "cannot convert extracted polyhedral model to OpenScop"
  | Some scop -> scop

let validate_components pp1 pp2 =
  let ((pil1, varctxt1), _) = pp1 in
  let ((pil2, _), _) = pp2 in
  let (wf1, wf1_ok) = SPolOpt.CoreOpt.check_wf_polyprog pp1 in
  let (wf2, wf2_ok) = SPolOpt.CoreOpt.check_wf_polyprog pp2 in
  let (eqdom, eqdom_ok) = SPolOpt.CoreOpt.coq_EqDom pp1 pp2 in
  let env_dim = nat_of_int (List.length varctxt1) in
  let pil_ext = SPolIRs.SPolIRs.PolyLang.compose_pinstrs_ext pil1 pil2 in
  let valid_access = SPolOpt.CoreOpt.check_valid_access pil_ext in
  let (res, res_ok) = SPolOpt.CoreOpt.validate_instr_list (List.rev pil_ext) env_dim in
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
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  dump_poly_payload "strengthened" pol;
  let inscop = poly_to_openscop pol in
  let (self_valid, self_ok) = SPolOpt.CoreOpt.validate pol pol in
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
  let (roundtrip_valid, roundtrip_ok) = SPolOpt.CoreOpt.validate pol pol_roundtrip in
  print_validate_components "validate(strengthened, roundtrip-before)" pol pol_roundtrip;
  let (complete_before_valid, complete_before_ok) = SPolOpt.CoreOpt.validate pol pol_complete_before in
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
  let (sched_valid, sched_ok) = SPolOpt.CoreOpt.validate pol pol_sched in
  print_validate_components "validate(strengthened, scheduled)" pol pol_sched;
  let (old_complete_sched_valid, old_complete_sched_ok) = SPolOpt.CoreOpt.validate pol_complete_before pol_sched in
  print_validate_components "validate(complete-before, scheduled)" pol_complete_before pol_sched;
  let (new_complete_sched_valid, new_complete_sched_ok) = SPolOpt.CoreOpt.validate pol pol_complete_after in
  print_validate_components "validate(strengthened, complete-after)" pol pol_complete_after;
  let (complete_sched_valid, complete_sched_ok) = SPolOpt.CoreOpt.validate pol_complete_before pol_complete_after in
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

let import_complete_spol_or_fail label scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into syntax polyhedral IR: %s"
        label
        (string_of_coq_err msg)

let import_faithful_spol_or_fail label base scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop base scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s faithfully into syntax IR: %s"
        label
        (string_of_coq_err msg)

let import_schedule_only_spol_or_fail label base scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only base scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s as schedule-only syntax IR: %s"
        label
        (string_of_coq_err msg)

let import_complete_tpol_or_fail label scop =
  match TPolIRs.TPolIRs.PolyLang.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into validator polyhedral IR: %s"
        label
        (string_of_coq_err msg)

let import_complete_tiling_or_fail label scop =
  match TPolOpt.Tiling.PL.from_openscop_complete scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s into tiling validator IR: %s"
        label
        (string_of_coq_err msg)

let required_vars_for_tiling_pinstr env_size pi =
  max_int
    (env_size + Camlcoq.Nat.to_int (TPolOpt.Tiling.PL.pi_depth pi))
    (max_int
       (List.length (TPolOpt.Tiling.PL.pi_poly pi))
       (List.length (TPolOpt.Tiling.PL.pi_schedule pi)))

let required_vars_for_tiling_pprog pp =
  let ((pis, ctxt), vars) = pp in
  let env_size = List.length ctxt in
  List.fold_left
    (fun acc pi -> max_int acc (required_vars_for_tiling_pinstr env_size pi))
    (List.length vars)
    pis

let pad_tiling_vars_to required ((pis, ctxt), vars) =
  let current = List.length vars in
  if current >= required then
    ((pis, ctxt), vars)
  else
    let rec add idx n acc =
      if n <= 0 then List.rev acc
      else
        let ident =
          Camlcoq.intern_string (Printf.sprintf "__tiling_pad_%d" idx)
        in
        add (idx + 1) (n - 1) ((ident, TPolIRs.TPolIRs.Ty.dummy) :: acc)
    in
    ((pis, ctxt), vars @ add current (required - current) [])

let normalize_tiling_validator_inputs before_pol after_pol =
  let required =
    max_int
      (required_vars_for_tiling_pprog before_pol)
      (required_vars_for_tiling_pprog after_pol)
  in
  (pad_tiling_vars_to required before_pol, pad_tiling_vars_to required after_pol)

let build_canonical_tiled_after before_pol ws =
  let ((before_pis, before_ctxt), before_vars) = before_pol in
  let env_size = nat_of_int (List.length before_ctxt) in
  let after_pis =
    List.map2
      (fun before_pi w ->
        let cw = TPolOpt.Tiling.compiled_pinstr_tiling_witness w in
        {
          TPolOpt.Tiling.PL.pi_depth =
            nat_of_int
              (Camlcoq.Nat.to_int (TPolOpt.Tiling.PL.pi_depth before_pi)
               + List.length w.stw_links);
          pi_instr = TPolOpt.Tiling.PL.pi_instr before_pi;
          pi_poly =
            (TPolOpt.Tiling.ptw_link_domain cw)
            @
            (TPolOpt.Tiling.lifted_base_domain_after_env
               env_size
               cw
               (TPolOpt.Tiling.PL.pi_poly before_pi));
          pi_schedule =
            TPolOpt.Tiling.lift_schedule_after_env
              (TPolOpt.Tiling.ptw_added_dims cw)
              env_size
              (TPolOpt.Tiling.PL.pi_schedule before_pi);
          pi_point_witness = PointWitness.PSWTiling w;
          pi_transformation = TPolOpt.Tiling.PL.pi_transformation before_pi;
          pi_access_transformation =
            TPolOpt.Tiling.PL.pi_access_transformation before_pi;
          pi_waccess = TPolOpt.Tiling.PL.pi_waccess before_pi;
          pi_raccess = TPolOpt.Tiling.PL.pi_raccess before_pi;
        })
      before_pis
      ws
  in
  ((after_pis, before_ctxt), before_vars)

let build_canonical_tiled_after_spol before_pol ws =
  let ((before_pis, before_ctxt), before_vars) = before_pol in
  let env_size = nat_of_int (List.length before_ctxt) in
  let after_pis =
    List.map2
      (fun before_pi w ->
        let cw = TPolOpt.Tiling.compiled_pinstr_tiling_witness w in
        let added_dims = TPolOpt.Tiling.ptw_added_dims cw in
        {
          SPolIRs.SPolIRs.PolyLang.pi_depth =
            nat_of_int
              (Camlcoq.Nat.to_int (SPolIRs.SPolIRs.PolyLang.pi_depth before_pi)
               + List.length w.stw_links);
          pi_instr = SPolIRs.SPolIRs.PolyLang.pi_instr before_pi;
          pi_poly =
            (TPolOpt.Tiling.ptw_link_domain cw)
            @
            (TPolOpt.Tiling.lifted_base_domain_after_env
               env_size
               cw
               (SPolIRs.SPolIRs.PolyLang.pi_poly before_pi));
          pi_schedule =
            TPolOpt.Tiling.lift_schedule_after_env
              added_dims
              env_size
              (SPolIRs.SPolIRs.PolyLang.pi_schedule before_pi);
          pi_point_witness = PointWitness.PSWTiling w;
          pi_transformation = SPolIRs.SPolIRs.PolyLang.pi_transformation before_pi;
          pi_access_transformation =
            SPolIRs.SPolIRs.PolyLang.pi_access_transformation before_pi;
          pi_waccess = SPolIRs.SPolIRs.PolyLang.pi_waccess before_pi;
          pi_raccess = SPolIRs.SPolIRs.PolyLang.pi_raccess before_pi;
        })
      before_pis
      ws
  in
  ((after_pis, before_ctxt), before_vars)

let required_vars_for_spol_pinstr env_size pi =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let access_width accs =
    List.fold_left
      (fun acc (_, affs) ->
        List.fold_left
          (fun acc' (zs, _) -> max_int acc' (List.length zs))
          acc
          affs)
      0
      accs
  in
  max_int
    (env_size + Camlcoq.Nat.to_int (PL.pi_depth pi))
    (max_int
       (List.fold_left
          (fun acc (zs, _) -> max_int acc (List.length zs))
          0
          (PL.pi_poly pi))
       (max_int
          (List.fold_left
             (fun acc (zs, _) -> max_int acc (List.length zs))
             0
             (PL.pi_schedule pi))
          (max_int
             (List.fold_left
                (fun acc (zs, _) -> max_int acc (List.length zs))
                0
                (PL.pi_transformation pi))
             (max_int
                (access_width (PL.pi_waccess pi))
                (access_width (PL.pi_raccess pi))))))

let required_vars_for_spol_pprog pp =
  let ((pis, ctxt), vars) = pp in
  let env_size = List.length ctxt in
  List.fold_left
    (fun acc pi -> max_int acc (required_vars_for_spol_pinstr env_size pi))
    (List.length vars)
    pis

let pad_spol_vars_to required ((pis, ctxt), vars) =
  let current = List.length vars in
  if current >= required then
    ((pis, ctxt), vars)
  else
    let rec add idx n acc =
      if n <= 0 then List.rev acc
      else
        let ident =
          Camlcoq.intern_string (Printf.sprintf "__tiling_codegen_pad_%d" idx)
        in
        add (idx + 1) (n - 1) ((ident, SPolIRs.SPolIRs.Ty.dummy) :: acc)
    in
    ((pis, ctxt), vars @ add current (required - current) [])

let normalize_spol_codegen_input pp =
  pad_spol_vars_to (required_vars_for_spol_pprog pp) pp

let count_spol_domain_rows ((pis, _ctxt), _vars) =
  List.fold_left
    (fun acc pi -> acc + List.length (SPolIRs.SPolIRs.PolyLang.pi_poly pi))
    0
    pis

let dedup_spol_codegen_domains ((pis, ctxt), vars) =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let dedup_pi (pi : PL.coq_PolyInstr) =
    { pi with pi_poly = PL.dedup_domain_rows (PL.pi_poly pi) }
  in
  ((List.map dedup_pi pis, ctxt), vars)

let maybe_dedup_spol_codegen_domains timings metrics pol =
  add_metric metrics "codegen_input.pis" (let ((pis, _), _) = pol in List.length pis);
  add_metric metrics "codegen_input.domain_rows" (count_spol_domain_rows pol);
  if debug_env_enabled "POLCERT_PROFILE_DEDUP_CODEGEN_DOMAINS" then
    let deduped =
      time_stage timings "dedup_codegen_domains" (fun () ->
        dedup_spol_codegen_domains pol)
    in
    add_metric metrics "codegen_dedup.pis" (let ((pis, _), _) = deduped in List.length pis);
    add_metric metrics "codegen_dedup.domain_rows" (count_spol_domain_rows deduped);
    deduped
  else
    pol

let normalize_stiling_validator_inputs before_pol after_pol =
  let required =
    max_int
      (required_vars_for_spol_pprog before_pol)
      (required_vars_for_spol_pprog after_pol)
  in
  (pad_spol_vars_to required before_pol, pad_spol_vars_to required after_pol)

let checked_tiling_schedule_canonical_validate before_pol after_pol ws =
  STilingCanonicalOpt.checked_tiling_schedule_canonical_validate
    before_pol
    after_pol
    ws

let checked_tiling_validate_with_canonical before_pol after_pol ws =
  let (canonical_res, canonical_ok) =
    checked_tiling_schedule_canonical_validate before_pol after_pol ws
  in
  if canonical_ok && canonical_res then
    (canonical_res, canonical_ok)
  else
    SPolOpt.CoreOpt.checked_tiling_validate before_pol after_pol ws

let checked_tiling_validate_with_bands before_pol after_pol ws =
  let (shape_res, shape_ok) =
    STilingBandSched.checked_tiling_schedule_stripmined_validate_poly
      before_pol
      after_pol
      ws
  in
  if not (shape_ok && shape_res) then
    (shape_res, shape_ok)
  else
    let before_t = STilingBandSched.outer_to_tiling_pprog before_pol in
    let after_t = STilingBandSched.outer_to_tiling_pprog after_pol in
    match STilingBandSched.infer_pprog_tiling_bands before_t ws with
    | None -> (false, true)
    | Some bands ->
        STilingBandSched.check_pprog_permutable_tiling_bands
          before_t
          after_t
          ws
          bands

let tiling_artifact_from_scops_or_fail
    ~second_level
    ~before_label
    ~after_label
    before_scop
    after_scop =
  let tiling_mode = pluto_tiling_mode second_level in
  try
    PlutoTilingValidator.extract_phase_artifact_from_scops
      ~tiling_mode
      ~before_path:before_label
      ~after_path:after_label
      before_scop
      after_scop
  with
  | PlutoTilingValidator.ValidationError msg ->
      frontend_failf
        "cannot extract tiling witness/artifact for %s -> %s: %s"
        before_label
        after_label
        msg

let canonicalize_tiled_after before_label after_label before_pol after_scop ws =
  let canonical_after = build_canonical_tiled_after before_pol ws in
  match TPolOpt.Tiling.PL.from_openscop_schedule_only canonical_after after_scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s as a schedule over the canonical tiled skeleton for %s: %s"
        after_label
        before_label
        (string_of_coq_err msg)

let affine_forward_scops before_label after_label before_scop after_scop =
  let before_pol = import_complete_tpol_or_fail before_label before_scop in
  let after_pol = import_complete_tpol_or_fail after_label after_scop in
  TPolValidator.validate before_pol after_pol

let run_affine_validator before_file after_file =
  let before_scop = read_openscop_or_fail before_file in
  let after_scop = read_openscop_or_fail after_file in
  let (res, ok) =
    affine_forward_scops before_file after_file before_scop after_scop
  in
  Printf.printf "before: %s\n" before_file;
  Printf.printf "after:  %s\n" after_file;
  Printf.printf "overall: %s\n" (if ok && res then "PASS" else "FAIL");
  if ok && res then 0 else 2

let tiling_forward_scops ~second_level ~before_label ~after_label before_scop after_scop =
  let before_pol = import_complete_spol_or_fail before_label before_scop in
  let artifact =
    tiling_artifact_from_scops_or_fail
      ~second_level
      ~before_label
      ~after_label
      before_scop
      after_scop
  in
  let ws = PhaseTiling.convert_witness artifact.artifact_witness in
  let after_pol =
    let canonical_after = build_canonical_tiled_after_spol before_pol ws in
    match SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only canonical_after artifact.artifact_after_scop with
    | Okk pol -> pol
    | Err msg ->
        frontend_failf
          "cannot import %s as a schedule over the canonical tiled skeleton for %s: %s"
          after_label
          before_label
          (string_of_coq_err msg)
  in
  let (before_pol, after_pol) =
    normalize_stiling_validator_inputs before_pol after_pol
  in
  if Scheduler.diamond_tiling_enabled () then
    checked_tiling_validate_with_bands before_pol after_pol ws
  else
    checked_tiling_validate_with_canonical before_pol after_pol ws

let extract_strengthened_poly loop =
  let pol0 = extract_poly loop in
  SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0

let checked_parallel_current_codegen_or_fail label pol dim =
  let plan = nat_of_int dim in
  let pol = normalize_spol_codegen_input pol in
  let (cert_res, cert_ok) =
    ParallelValidatorCore.checked_parallelize_current
      (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol)
      plan
  in
  if not cert_ok then
    frontend_failf "%s: extracted parallel validator raised an alarm" label;
  match cert_res with
  | Err msg ->
      frontend_failf
        "%s: checked parallelization failed: %s"
        label
        (string_of_coq_err msg)
  | Okk cert ->
      let (codegen_res, codegen_ok) =
        ParallelCodegenCore.checked_annotated_codegen
          (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol)
          cert
      in
      if not codegen_ok then
        frontend_failf "%s: extracted parallel codegen raised an alarm" label;
      match codegen_res with
      | Okk pl -> pl
      | Err msg ->
          frontend_failf
            "%s: checked parallel codegen failed: %s"
            label
            (string_of_coq_err msg)

let checked_vector_current_codegen_or_fail label pol dim =
  let plan = nat_of_int dim in
  let pol = normalize_spol_codegen_input pol in
  let current = SPolIRs.SPolIRs.PolyLang.current_view_pprog pol in
  let (cert_res, cert_ok) =
    ParallelValidatorCore.checked_parallelize_current current plan
  in
  if not cert_ok then
    frontend_failf "%s: extracted vector validator raised an alarm" label;
  match cert_res with
  | Err msg ->
      frontend_failf
        "%s: checked vectorization failed: %s"
        label
        (string_of_coq_err msg)
  | Okk cert ->
      let (codegen_res, codegen_ok) =
        ParallelCodegenCore.checked_vector_annotated_codegen current cert
      in
      if not codegen_ok then
        frontend_failf "%s: extracted vector codegen raised an alarm" label;
      match codegen_res with
      | Okk pl -> pl
      | Err msg ->
          frontend_failf
            "%s: checked vector codegen failed: %s"
            label
            (string_of_coq_err msg)

let try_checked_parallel_current_codegen pol dim =
  let plan = nat_of_int dim in
  let pol = normalize_spol_codegen_input pol in
  let current = SPolIRs.SPolIRs.PolyLang.current_view_pprog pol in
  let (cert_res, cert_ok) =
    ParallelValidatorCore.checked_parallelize_current current plan
  in
  if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
    begin match cert_res with
    | Okk _ ->
        Printf.eprintf
          "[debug-parallel] checked_parallelize_current dim=%d => accepted(ok=%b)\n"
          dim cert_ok
    | Err msg ->
        Printf.eprintf
          "[debug-parallel] checked_parallelize_current dim=%d => rejected(ok=%b,msg=%s)\n"
          dim cert_ok (string_of_coq_err msg)
    end;
  if not cert_ok then
    None
  else
    match cert_res with
    | Err _ -> None
    | Okk cert ->
        let (codegen_res, codegen_ok) =
          ParallelCodegenCore.checked_annotated_codegen current cert
        in
        if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
          begin match codegen_res with
          | Okk _ ->
              Printf.eprintf
                "[debug-parallel] checked_annotated_codegen dim=%d => accepted(ok=%b)\n"
                dim codegen_ok
          | Err msg ->
              Printf.eprintf
                "[debug-parallel] checked_annotated_codegen dim=%d => rejected(ok=%b,msg=%s)\n"
                dim codegen_ok (string_of_coq_err msg)
          end;
        if not codegen_ok then
          None
        else
          match codegen_res with
          | Okk pl -> Some pl
          | Err _ -> None

let try_checked_vector_current_codegen pol dim =
  let plan = nat_of_int dim in
  let pol = normalize_spol_codegen_input pol in
  let current = SPolIRs.SPolIRs.PolyLang.current_view_pprog pol in
  let (cert_res, cert_ok) =
    ParallelValidatorCore.checked_parallelize_current current plan
  in
  if debug_env_enabled "POLCERT_DEBUG_VECTOR_HINT" then
    begin match cert_res with
    | Okk _ ->
        Printf.eprintf
          "[debug-vector] checked_parallelize_current dim=%d => accepted(ok=%b)\n"
          dim cert_ok
    | Err msg ->
        Printf.eprintf
          "[debug-vector] checked_parallelize_current dim=%d => rejected(ok=%b,msg=%s)\n"
          dim cert_ok (string_of_coq_err msg)
    end;
  if not cert_ok then
    None
  else
    match cert_res with
    | Err _ -> None
    | Okk cert ->
        let (codegen_res, codegen_ok) =
          ParallelCodegenCore.checked_vector_annotated_codegen current cert
        in
        if debug_env_enabled "POLCERT_DEBUG_VECTOR_HINT" then
          begin match codegen_res with
          | Okk _ ->
              Printf.eprintf
                "[debug-vector] checked_vector_annotated_codegen dim=%d => accepted(ok=%b)\n"
                dim codegen_ok
          | Err msg ->
              Printf.eprintf
                "[debug-vector] checked_vector_annotated_codegen dim=%d => rejected(ok=%b,msg=%s)\n"
                dim codegen_ok (string_of_coq_err msg)
          end;
        if not codegen_ok then
          None
        else
          match codegen_res with
          | Okk pl -> Some pl
          | Err _ -> None

let tag_loop_for_parallel_pretty loop =
  ParallelCodegenCore.tag_loop loop

let tagged_prepared_codegen pol =
  let (loop, ok) =
    SPolOpt.CoreOpt.Prepare.prepared_codegen (normalize_spol_codegen_input pol)
  in
  (tag_loop_for_parallel_pretty loop, ok)

let debug_parallel_hint_if name hints =
  if debug_env_enabled name then
    match hints with
    | [] ->
        Printf.eprintf "[debug-parallel] no Pluto loop hint found\n"
    | _ ->
        List.iter
          (fun hint ->
             Printf.eprintf
               "[debug-parallel] Pluto hint iterator=%s current_dim=%d\n"
               hint.Scheduler.hint_iterator
               hint.Scheduler.hint_current_dim)
          hints

let debug_vector_hint_if name hints =
  if debug_env_enabled name then
    match hints with
    | [] ->
        Printf.eprintf "[debug-vector] no Pluto vector loop hint found\n"
    | _ ->
        List.iter
          (fun hint ->
             Printf.eprintf
               "[debug-vector] Pluto vector hint iterator=%s current_dim=%d directive=%d\n"
               hint.Scheduler.hint_iterator
               hint.Scheduler.hint_current_dim
               hint.Scheduler.hint_directive)
          hints

let hint_dims hints =
  List.map (fun hint -> hint.Scheduler.hint_current_dim) hints

let first_hint_dim hints =
  match hint_dims hints with
  | [] -> None
  | dim :: _ -> Some dim

let debug_parallel_dim_scan_if name pol =
  if debug_env_enabled name then
    let current = SPolIRs.SPolIRs.PolyLang.current_view_pprog (normalize_spol_codegen_input pol) in
    let rec scan dim failures_left =
      if failures_left <= 0 then ()
      else
        let (res, ok) =
          ParallelValidatorCore.checked_parallelize_current current (nat_of_int dim)
        in
        begin match res with
        | Okk _ ->
            Printf.eprintf
              "[debug-parallel] current-dim %d: accepted(ok=%b)\n"
              dim ok
        | Err msg ->
            Printf.eprintf
              "[debug-parallel] current-dim %d: rejected(ok=%b,msg=%s)\n"
              dim ok (string_of_coq_err msg)
        end;
        scan (dim + 1) (failures_left - 1)
    in
    scan 0 8

let max_current_depth_spol_pprog pp =
  let ((pis, _ctxt), _vars) = pp in
  List.fold_left
    (fun acc pi -> max_int acc (int_of_nat (SPolIRs.SPolIRs.PolyLang.pi_depth pi)))
    0
    pis

let rec int_range lo hi =
  if lo >= hi then [] else lo :: int_range (lo + 1) hi

let unique_ints xs =
  let rec go seen acc = function
    | [] -> List.rev acc
    | x :: rest ->
        if List.mem x seen then go seen acc rest
        else go (x :: seen) (x :: acc) rest
  in
  go [] [] xs

let parallel_candidate_dims pol hint_dim =
  let current = SPolIRs.SPolIRs.PolyLang.current_view_pprog (normalize_spol_codegen_input pol) in
  let depth = max_current_depth_spol_pprog current in
  let all = int_range 0 depth in
  match hint_dim with
  | None -> all
  | Some d -> d :: List.filter (fun x -> x <> d) all

let try_pluto_hint_preferred_parallel_codegen pol hint_dim =
  let dims = parallel_candidate_dims pol hint_dim in
  let rec go = function
    | [] -> None
    | dim :: rest ->
        begin match try_checked_parallel_current_codegen pol dim with
        | Some pl ->
            let used_hint =
              match hint_dim with
              | Some hinted -> hinted = dim
              | None -> false
            in
            Some (pl, used_hint)
        | None -> go rest
        end
  in
  go dims

let try_pluto_parallel_codegen pol hint_dim strict =
  match hint_dim with
  | Some dim when strict ->
      begin match try_checked_parallel_current_codegen pol dim with
      | Some pl -> Some (pl, true)
      | None -> None
      end
  | None when strict ->
      None
  | _ ->
      try_pluto_hint_preferred_parallel_codegen pol hint_dim

let try_pluto_hint_preferred_vector_codegen pol hint_dim =
  let dims = parallel_candidate_dims pol hint_dim in
  let rec go = function
    | [] -> None
    | dim :: rest ->
        begin match try_checked_vector_current_codegen pol dim with
        | Some pl ->
            let used_hint =
              match hint_dim with
              | Some hinted -> hinted = dim
              | None -> false
            in
            Some (pl, used_hint)
        | None -> go rest
        end
  in
  go dims

let try_pluto_vector_codegen pol hint_dim strict =
  match hint_dim with
  | Some dim when strict ->
      begin match try_checked_vector_current_codegen pol dim with
      | Some pl -> Some (pl, true)
      | None -> None
      end
  | None when strict ->
      None
  | _ ->
      try_pluto_hint_preferred_vector_codegen pol hint_dim

let parallel_multipar_candidate_dims pol hinted_dims strict =
  let hinted_dims = unique_ints hinted_dims in
  if strict then
    hinted_dims
  else
    let current = SPolIRs.SPolIRs.PolyLang.current_view_pprog (normalize_spol_codegen_input pol) in
    let depth = max_current_depth_spol_pprog current in
    unique_ints (hinted_dims @ int_range 0 depth)

let try_checked_parallel_current_codegen_many pol dims =
  let dims = unique_ints dims in
  let pol = normalize_spol_codegen_input pol in
  let current = SPolIRs.SPolIRs.PolyLang.current_view_pprog pol in
  let rec collect accepted_dims accepted_certs = function
    | [] -> (List.rev accepted_dims, List.rev accepted_certs)
    | _ when List.length accepted_dims >= 2 ->
        (List.rev accepted_dims, List.rev accepted_certs)
    | dim :: rest ->
        let (cert_res, cert_ok) =
          ParallelValidatorCore.checked_parallelize_current current (nat_of_int dim)
        in
        if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
          begin match cert_res with
          | Okk _ ->
              Printf.eprintf
                "[debug-parallel] multipar candidate dim=%d => accepted(ok=%b)\n"
                dim cert_ok
          | Err msg ->
              Printf.eprintf
                "[debug-parallel] multipar candidate dim=%d => rejected(ok=%b,msg=%s)\n"
                dim cert_ok (string_of_coq_err msg)
          end;
        if not cert_ok then
          collect accepted_dims accepted_certs rest
        else
          match cert_res with
          | Okk cert -> collect (dim :: accepted_dims) (cert :: accepted_certs) rest
          | Err _ -> collect accepted_dims accepted_certs rest
  in
  let (accepted_dims, certs) = collect [] [] dims in
  match certs with
  | [] -> None
  | _ ->
      let (codegen_res, codegen_ok) =
        ParallelCodegenCore.checked_annotated_codegen_many current certs
      in
      if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
        begin match codegen_res with
        | Okk _ ->
            Printf.eprintf
              "[debug-parallel] checked_annotated_codegen_many dims=[%s] => accepted(ok=%b)\n"
              (String.concat "," (List.map string_of_int accepted_dims))
              codegen_ok
        | Err msg ->
            Printf.eprintf
              "[debug-parallel] checked_annotated_codegen_many dims=[%s] => rejected(ok=%b,msg=%s)\n"
              (String.concat "," (List.map string_of_int accepted_dims))
              codegen_ok
              (string_of_coq_err msg)
        end;
      if not codegen_ok then
        None
      else
        match codegen_res with
        | Okk pl -> Some (pl, accepted_dims)
        | Err _ -> None

let try_pluto_multipar_codegen pol hinted_dims strict =
  let candidates = parallel_multipar_candidate_dims pol hinted_dims strict in
  match try_checked_parallel_current_codegen_many pol candidates with
  | None -> None
  | Some (pl, accepted_dims) ->
      let used_hint =
        List.exists (fun dim -> List.mem dim hinted_dims) accepted_dims
      in
      Some (pl, used_hint)

let try_extracted_diamond_parallel_current use_iss loop dim =
  try
    let (pl, ok) =
      (if use_iss then
         SParallelPolOpt.opt_parallel_current_diamond_with_iss
       else
         SParallelPolOpt.opt_parallel_current_diamond)
        loop
        (nat_of_int dim)
    in
    if ok then Some pl else None
  with
  | CertcheckerConfig.CertCheckerFailure _ -> None

let try_extracted_diamond_vector_current use_iss loop dim =
  try
    let (pl, ok) =
      (if use_iss then
         SParallelPolOpt.opt_vector_current_diamond_with_iss
       else
         SParallelPolOpt.opt_vector_current_diamond)
        loop
        (nat_of_int dim)
    in
    if ok then Some pl else None
  with
  | CertcheckerConfig.CertCheckerFailure _ -> None

let try_extracted_diamond_parallel_many use_iss loop dims =
  try
    let dims = List.map nat_of_int dims in
    let (pl, ok) =
      (if use_iss then
         SParallelPolOpt.opt_parallel_current_many_diamond_with_iss
       else
         SParallelPolOpt.opt_parallel_current_many_diamond)
        loop
        dims
    in
    if ok then Some pl else None
  with
  | CertcheckerConfig.CertCheckerFailure _ -> None

let diamond_parallel_candidate_dims hint_dim =
  let fallback_dims = int_range 0 8 in
  match hint_dim with
  | Some d -> d :: List.filter (fun x -> x <> d) fallback_dims
  | None -> fallback_dims

let diamond_multipar_candidate_dims hinted_dims strict =
  let hinted_dims = unique_ints hinted_dims in
  if strict then
    hinted_dims
  else
    unique_ints (hinted_dims @ int_range 0 8)

let try_diamond_parallel_codegen use_iss loop hint_dim strict =
  let dims =
    match hint_dim, strict with
    | Some d, true -> [d]
    | None, true -> []
    | _ -> diamond_parallel_candidate_dims hint_dim
  in
  let rec go = function
    | [] -> None
    | dim :: rest ->
        begin match try_extracted_diamond_parallel_current use_iss loop dim with
        | Some pl ->
            let used_hint =
              match hint_dim with
              | Some hinted -> hinted = dim
              | None -> false
            in
            Some (pl, used_hint)
        | None -> go rest
        end
  in
  go dims

let try_diamond_vector_codegen use_iss loop hint_dim strict =
  let dims =
    match hint_dim, strict with
    | Some d, true -> [d]
    | None, true -> []
    | _ -> diamond_parallel_candidate_dims hint_dim
  in
  let rec go = function
    | [] -> None
    | dim :: rest ->
        begin match try_extracted_diamond_vector_current use_iss loop dim with
        | Some pl ->
            let used_hint =
              match hint_dim with
              | Some hinted -> hinted = dim
              | None -> false
            in
            Some (pl, used_hint)
        | None -> go rest
        end
  in
  go dims

let try_diamond_multipar_codegen use_iss loop hinted_dims strict =
  let dims = diamond_multipar_candidate_dims hinted_dims strict in
  match dims with
  | [] -> None
  | _ ->
      begin match try_extracted_diamond_parallel_many use_iss loop dims with
      | Some pl -> Some (pl, hinted_dims <> [])
      | None -> None
      end

let checked_affine_schedule_or_fail pol =
  let (pol', ok) = SPolOpt.CoreOpt.checked_affine_schedule pol in
  if not ok then
    frontend_failf "affine scheduling raised an extracted alarm before parallel codegen";
  pol'

type 'a phase_pipeline_artifacts = {
  phase_mid_scop : 'a;
  phase_tiling_scop : 'a;
  phase_after_scop : 'a;
  phase_has_final_affine : bool;
}

let current_midpoint_label () =
  if Scheduler.diamond_tiling_enabled () then
    diamond_midpoint_label (Scheduler.full_diamond_tiling_enabled ())
  else
    "mid_affine"

let current_tiling_label () =
  if Scheduler.diamond_tiling_enabled () then
    "posttile_diamond"
  else
    "after_tiled"

let current_final_after_label () =
  if Scheduler.diamond_tiling_enabled () then
    "after_rescheduled"
  else
    "after_tiled"

let phase_pipeline_artifacts_or_fail before_scop =
  if Scheduler.diamond_tiling_enabled () then
    match Scheduler.run_pluto_diamond_phase_pipeline before_scop with
    | Err msg ->
        frontend_failf
          "diamond Pluto phase pipeline failed: %s"
          (string_of_coq_err msg)
    | Okk (mid_scop, posttile_scop, after_scop) ->
        {
          phase_mid_scop = mid_scop;
          phase_tiling_scop = posttile_scop;
          phase_after_scop = after_scop;
          phase_has_final_affine = true;
        }
  else
    match Scheduler.run_pluto_phase_pipeline before_scop with
    | Err msg ->
        frontend_failf
          "phase-aligned Pluto pipeline failed: %s"
          (string_of_coq_err msg)
    | Okk (mid_scop, after_scop) ->
        {
          phase_mid_scop = mid_scop;
          phase_tiling_scop = after_scop;
          phase_after_scop = after_scop;
          phase_has_final_affine = false;
        }

let phase_pipeline_scops_or_fail before_scop =
  let artifacts = phase_pipeline_artifacts_or_fail before_scop in
  (artifacts.phase_mid_scop, artifacts.phase_after_scop)

let pluto_phase_scops loop =
  let pol0 = extract_poly loop in
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  let before_scop = poly_to_openscop pol in
  let artifacts = phase_pipeline_artifacts_or_fail before_scop in
  (before_scop, artifacts.phase_mid_scop, artifacts.phase_after_scop)

let pluto_phase_scops_with_iss loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.run_pluto_phase_pipeline_with_iss before_scop with
  | Err _ -> None
  | Okk (mid_scop, after_scop) -> Some (pol, before_scop, mid_scop, after_scop)

let pluto_phase_scops_with_iss_and_parallel_hint loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.run_pluto_phase_pipeline_with_iss_with_parallel_hint before_scop with
  | Err _ -> None
  | Okk (mid_scop, after_scop, hint) ->
      Some (pol, before_scop, mid_scop, after_scop, hint)

let pluto_phase_scops_with_iss_and_vector_hint loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.run_pluto_phase_pipeline_with_iss_with_vector_hint before_scop with
  | Err _ -> None
  | Okk (mid_scop, after_scop, hint) ->
      Some (pol, before_scop, mid_scop, after_scop, hint)

let pluto_phase_scops_with_parallel_hint loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.run_pluto_phase_pipeline_with_parallel_hint before_scop with
  | Err _ -> None
  | Okk (mid_scop, after_scop, hint) ->
      Some (pol, before_scop, mid_scop, after_scop, hint)

let pluto_phase_scops_with_vector_hint loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.run_pluto_phase_pipeline_with_vector_hint before_scop with
  | Err _ -> None
  | Okk (mid_scop, after_scop, hint) ->
      Some (pol, before_scop, mid_scop, after_scop, hint)

let pluto_diamond_parallel_hint cfg loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let runner =
    if cfg.force_iss then
      Scheduler.run_pluto_diamond_parallel_hint_with_iss
    else
      Scheduler.run_pluto_diamond_parallel_hint
  in
  match runner before_scop with
  | Err _ -> []
  | Okk hint -> hint

let pluto_diamond_vector_hint cfg loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let runner =
    if cfg.force_iss then
      Scheduler.run_pluto_diamond_vector_hint_with_iss
    else
      Scheduler.run_pluto_diamond_vector_hint
  in
  match runner before_scop with
  | Err _ -> []
  | Okk hint -> hint

let debug_generic_tiling_runtime loop =
  let pol0 = extract_poly loop in
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  let before_scop = poly_to_openscop pol in
  let midpoint_label = current_midpoint_label () in
  let tiling_label = current_tiling_label () in
  let final_after_label = current_final_after_label () in
  let artifacts = phase_pipeline_artifacts_or_fail before_scop in
  let mid_scop = artifacts.phase_mid_scop in
  let tiling_scop = artifacts.phase_tiling_scop in
  let after_scop = artifacts.phase_after_scop in
  let pol_mid = import_faithful_spol_or_fail midpoint_label pol mid_scop in
  let (aff_res, aff_ok) = SPolOpt.CoreOpt.validate pol pol_mid in
  let artifact =
    tiling_artifact_from_scops_or_fail
      ~second_level:(Scheduler.second_level_tiling_enabled ())
      ~before_label:midpoint_label
      ~after_label:tiling_label
      mid_scop
      tiling_scop
  in
  let ws = PhaseTiling.convert_witness artifact.artifact_witness in
  let pol_after =
    let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
    match
      SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only
        canonical_after
        artifact.artifact_after_scop
    with
    | Okk pol' -> pol'
    | Err msg ->
        frontend_failf "cannot import after_tiled over canonical skeleton: %s"
          (string_of_coq_err msg)
  in
  let final_affine =
    if artifacts.phase_has_final_affine then
      let (res, ok) =
        affine_forward_scops tiling_label final_after_label tiling_scop after_scop
      in
      Some (res, ok)
    else
      None
  in
  let before_t = SPolOpt.CoreOpt.outer_to_tiling_pprog pol_mid in
  let after_t = SPolOpt.CoreOpt.outer_to_tiling_pprog pol_after in
  let struct_ok =
    SPolOpt.CoreOpt.check_pprog_tiling_sourceb before_t after_t ws
  in
  let (checked_canonical_res, checked_canonical_ok) =
    checked_tiling_schedule_canonical_validate pol_mid pol_after ws
  in
  let (checked_res, checked_ok) =
    checked_tiling_validate_with_canonical pol_mid pol_after ws
  in
  let (pol_mid_norm, pol_after_norm) =
    normalize_stiling_validator_inputs pol_mid pol_after
  in
  let (checked_norm_canonical_res, checked_norm_canonical_ok) =
    checked_tiling_schedule_canonical_validate pol_mid_norm pol_after_norm ws
  in
  let (checked_norm_res, checked_norm_ok) =
    checked_tiling_validate_with_canonical pol_mid_norm pol_after_norm ws
  in
  begin match final_affine with
  | Some (final_res, final_ok) ->
      Printf.eprintf
        "[debug-generic-tiling] affine=%b(ok=%b) struct=%b canonical=%b(ok=%b) checked=%b(ok=%b) canonical_norm=%b(ok=%b) checked_norm=%b(ok=%b) final_affine=%b(ok=%b)\n"
        aff_res aff_ok struct_ok
        checked_canonical_res checked_canonical_ok
        checked_res checked_ok
        checked_norm_canonical_res checked_norm_canonical_ok
        checked_norm_res checked_norm_ok
        final_res final_ok
  | None ->
      Printf.eprintf
        "[debug-generic-tiling] affine=%b(ok=%b) struct=%b canonical=%b(ok=%b) checked=%b(ok=%b) canonical_norm=%b(ok=%b) checked_norm=%b(ok=%b)\n"
        aff_res aff_ok struct_ok
        checked_canonical_res checked_canonical_ok
        checked_res checked_ok
        checked_norm_canonical_res checked_norm_canonical_ok
        checked_norm_res checked_norm_ok
  end;
  dump_poly_payload "generic-mid(like-source)" pol_mid;
  dump_poly_payload "generic-after(canonical-schedule-only)" pol_after;
  dump_poly_payload "generic-mid(normalized)" pol_mid_norm;
  dump_poly_payload "generic-after(normalized)" pol_after_norm

let debug_band_tiling_runtime loop =
  let pol0 = extract_poly loop in
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  let before_scop = poly_to_openscop pol in
  let midpoint_label = current_midpoint_label () in
  let tiling_label = current_tiling_label () in
  let final_after_label = current_final_after_label () in
  let artifacts = phase_pipeline_artifacts_or_fail before_scop in
  let mid_scop = artifacts.phase_mid_scop in
  let tiling_scop = artifacts.phase_tiling_scop in
  let after_scop = artifacts.phase_after_scop in
  let pol_mid = import_faithful_spol_or_fail midpoint_label pol mid_scop in
  let artifact =
    tiling_artifact_from_scops_or_fail
      ~second_level:(Scheduler.second_level_tiling_enabled ())
      ~before_label:midpoint_label
      ~after_label:tiling_label
      mid_scop
      tiling_scop
  in
  let ws = PhaseTiling.convert_witness artifact.artifact_witness in
  let pol_after =
    let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
    match
      SPolIRs.SPolIRs.PolyLang.from_openscop_schedule_only
        canonical_after
        artifact.artifact_after_scop
    with
    | Okk pol' -> pol'
    | Err msg ->
        frontend_failf "cannot import after_tiled over canonical skeleton: %s"
          (string_of_coq_err msg)
  in
  let before_t = STilingBandSched.outer_to_tiling_pprog pol_mid in
  let after_t = STilingBandSched.outer_to_tiling_pprog pol_after in
  let (shape_res, shape_ok) =
    STilingBandSched.checked_tiling_schedule_stripmined_validate_poly pol_mid pol_after ws
  in
  let bands_opt = STilingBandSched.infer_pprog_tiling_bands before_t ws in
  let perm_res, perm_ok, perm_direct_res, perm_direct_ok, perm_pluto_res, perm_pluto_ok, band_count =
    match bands_opt with
    | Some bands ->
        let (res, ok) =
          STilingBandSched.check_pprog_permutable_tiling_bands before_t after_t ws bands
        in
        let (res_direct, ok_direct) =
          STilingBandSched.check_pprog_permutable_tiling_bands_direct
            before_t after_t ws bands
        in
        let (res_pluto, ok_pluto) =
          STilingBandSched.check_pprog_pluto_permutable_tiling_bands_strong
            before_t after_t ws bands
        in
        (res, ok, res_direct, ok_direct, res_pluto, ok_pluto, List.length bands)
    | None -> (false, false, false, false, false, false, 0)
  in
  begin match bands_opt with
  | Some bands ->
      if debug_env_enabled "POLCERT_DEBUG_BAND_TILING" then
        List.iteri
          (fun i band ->
             Printf.eprintf
               "[debug-band-tiling] band[%d]=start:%d len:%d cutoff:%d\n"
               i
               (int_of_nat (STilingBandSched.CoreBandSched.ptb_start band))
               (int_of_nat (STilingBandSched.CoreBandSched.ptb_len band))
               (int_of_nat (STilingBandSched.CoreBandSched.ptb_start band)
                + (2 * int_of_nat (STilingBandSched.CoreBandSched.ptb_len band))))
          bands;
      let ((before_pis, before_ctxt), before_vars) = before_t in
      let ((after_pis, _after_ctxt), _after_vars) = after_t in
      if debug_env_enabled "POLCERT_DEBUG_BAND_TILING" then begin
        let env_size = List.length before_ctxt in
        let env_size_nat = nat_of_int env_size in
        let composed =
          STilingBandSched.CoreBandSched.Tiling.compose_tiling_pinstrs_ext_from_after
            env_size_nat before_pis after_pis ws
        in
        dump_bandaffine_payload "band-composed" env_size composed;
        debug_bandaffine_pair_checks "band-composed" env_size_nat composed;
        begin match STilingBandSched.CoreBandSched.infer_common_tiling_band bands with
        | Some common_band ->
            begin match
              STilingBandSched.CoreBandSched.project_pinstrs_ext_with_pluto_phased_band
                composed ws common_band
            with
            | Some projected ->
                dump_bandaffine_payload "band-pluto-projected" env_size projected;
                debug_bandaffine_pair_checks "band-pluto-projected" env_size_nat projected
            | None ->
                Printf.eprintf
                  "[debug] band-pluto-projected unavailable\n"
            end
        | None ->
            Printf.eprintf
              "[debug] common band inference failed for projected debug\n"
        end
      end;
      let rec debug_one i befores afters ws bands =
        match befores, afters, ws, bands with
        | before_pi :: befores', after_pi :: afters', w :: ws', band :: bands' ->
            let before_one = (([before_pi], before_ctxt), before_vars) in
            let after_one = (([after_pi], before_ctxt), before_vars) in
            let (res_i, ok_i) =
              STilingBandSched.check_pprog_permutable_tiling_bands
                before_one
                after_one
                [w]
                [band]
            in
            Printf.eprintf
              "[debug-band-tiling] stmt[%d] single-band perm=%b(ok=%b)\n"
              i res_i ok_i;
            debug_one (i + 1) befores' afters' ws' bands'
        | _, _, _, _ -> ()
      in
      debug_one 0 before_pis after_pis ws bands
  | None -> ()
  end;
  let (generic_res, generic_ok) =
    checked_tiling_validate_with_canonical pol_mid pol_after ws
  in
  let final_affine =
    if artifacts.phase_has_final_affine then
      let (res, ok) =
        affine_forward_scops tiling_label final_after_label tiling_scop after_scop
      in
      Some (res, ok)
    else
      None
  in
  begin match final_affine with
  | Some (final_res, final_ok) ->
      Printf.eprintf
        "[debug-band-tiling] shape=%b(ok=%b) bands=%d infer=%b perm=%b(ok=%b) direct=%b(ok=%b) pluto=%b(ok=%b) generic=%b(ok=%b) final_affine=%b(ok=%b)\n"
        shape_res shape_ok band_count (Option.is_some bands_opt)
        perm_res perm_ok
        perm_direct_res perm_direct_ok
        perm_pluto_res perm_pluto_ok
        generic_res generic_ok final_res final_ok
  | None ->
      Printf.eprintf
        "[debug-band-tiling] shape=%b(ok=%b) bands=%d infer=%b perm=%b(ok=%b) direct=%b(ok=%b) pluto=%b(ok=%b) generic=%b(ok=%b)\n"
        shape_res shape_ok band_count (Option.is_some bands_opt)
        perm_res perm_ok
        perm_direct_res perm_direct_ok
        perm_pluto_res perm_pluto_ok
        generic_res generic_ok
  end;
  dump_poly_payload "band-mid(like-source)" pol_mid;
  dump_poly_payload "band-after(canonical-schedule-only)" pol_after

let dump_scheduled_openscop loop =
  let (_, _, after_scop) = pluto_phase_scops loop in
  print_endline "== Scheduled OpenScop ==";
  OpenScopPrinter.openscop_printer' stdout after_scop;
  print_newline ()

let dump_scheduled_openscop_with_parallel cfg loop =
  if cfg.force_iss && cfg.force_notile then
    let pol = extract_strengthened_poly loop in
    let before_scop = poly_to_openscop pol in
    begin
      match Scheduler.affine_only_scop_scheduler_with_iss_with_parallel_hint before_scop with
      | Err msg ->
          frontend_failf
            "parallel ISS affine Pluto scheduling failed: %s"
            (string_of_coq_err msg)
      | Okk (mid_scop, _hint) ->
          print_endline "== Scheduled OpenScop ==";
          OpenScopPrinter.openscop_printer' stdout mid_scop;
          print_newline ()
    end
  else if cfg.force_iss then
    match pluto_phase_scops_with_iss_and_parallel_hint loop with
    | None ->
        frontend_failf "parallel ISS Pluto phase pipeline failed"
    | Some (_pol, _before_scop, _mid_scop, after_scop, _hint) ->
        print_endline "== Scheduled OpenScop ==";
        OpenScopPrinter.openscop_printer' stdout after_scop;
        print_newline ()

  else if cfg.force_notile then
    let pol = extract_strengthened_poly loop in
    let before_scop = poly_to_openscop pol in
    begin
      match Scheduler.affine_only_scop_scheduler_with_parallel_hint before_scop with
      | Err msg ->
          frontend_failf
            "parallel affine Pluto scheduling failed: %s"
            (string_of_coq_err msg)
      | Okk (mid_scop, _hint) ->
          print_endline "== Scheduled OpenScop ==";
          OpenScopPrinter.openscop_printer' stdout mid_scop;
          print_newline ()
    end
  else
    match pluto_phase_scops_with_parallel_hint loop with
    | None ->
        frontend_failf "parallel Pluto phase pipeline failed"
    | Some (_pol, _before_scop, _mid_scop, after_scop, _hint) ->
        print_endline "== Scheduled OpenScop ==";
        OpenScopPrinter.openscop_printer' stdout after_scop;
        print_newline ()

let dump_scheduled_openscop_with_vector cfg loop =
  if cfg.force_iss && cfg.force_notile then
    let pol = extract_strengthened_poly loop in
    let before_scop = poly_to_openscop pol in
    begin
      match Scheduler.affine_only_scop_scheduler_with_iss_with_vector_hint before_scop with
      | Err msg ->
          frontend_failf
            "vector ISS affine Pluto scheduling failed: %s"
            (string_of_coq_err msg)
      | Okk (mid_scop, _hint) ->
          print_endline "== Scheduled OpenScop ==";
          OpenScopPrinter.openscop_printer' stdout mid_scop;
          print_newline ()
    end
  else if cfg.force_iss then
    match pluto_phase_scops_with_iss_and_vector_hint loop with
    | None ->
        frontend_failf "vector ISS Pluto phase pipeline failed"
    | Some (_pol, _before_scop, _mid_scop, after_scop, _hint) ->
        print_endline "== Scheduled OpenScop ==";
        OpenScopPrinter.openscop_printer' stdout after_scop;
        print_newline ()
  else if cfg.force_notile then
    let pol = extract_strengthened_poly loop in
    let before_scop = poly_to_openscop pol in
    begin
      match Scheduler.affine_only_scop_scheduler_with_vector_hint before_scop with
      | Err msg ->
          frontend_failf
            "vector affine Pluto scheduling failed: %s"
            (string_of_coq_err msg)
      | Okk (mid_scop, _hint) ->
          print_endline "== Scheduled OpenScop ==";
          OpenScopPrinter.openscop_printer' stdout mid_scop;
          print_newline ()
    end
  else
    match pluto_phase_scops_with_vector_hint loop with
    | None ->
        frontend_failf "vector Pluto phase pipeline failed"
    | Some (_pol, _before_scop, _mid_scop, after_scop, _hint) ->
        print_endline "== Scheduled OpenScop ==";
        OpenScopPrinter.openscop_printer' stdout after_scop;
        print_newline ()

let optimize_with_phase_aligned_pluto loop =
  let pol0 = extract_poly loop in
  let pol = SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0 in
  let before_scop = poly_to_openscop pol in
  let midpoint_label = current_midpoint_label () in
  let tiling_label = current_tiling_label () in
  let final_after_label = current_final_after_label () in
  let artifacts = phase_pipeline_artifacts_or_fail before_scop in
  let mid_scop = artifacts.phase_mid_scop in
  let tiling_scop = artifacts.phase_tiling_scop in
  let after_scop = artifacts.phase_after_scop in
  let (affine_res, affine_ok) =
    affine_forward_scops "before" midpoint_label before_scop mid_scop
  in
  if not (affine_ok && affine_res) then
    (loop, false)
  else
    let (tiling_res, tiling_ok) =
      tiling_forward_scops
        ~second_level:(Scheduler.second_level_tiling_enabled ())
        ~before_label:midpoint_label
        ~after_label:tiling_label
        mid_scop
        tiling_scop
    in
    if not (tiling_ok && tiling_res) then
      (loop, false)
    else
      let (final_affine_res, final_affine_ok) =
        if artifacts.phase_has_final_affine then
          affine_forward_scops tiling_label final_after_label tiling_scop after_scop
        else
          (true, true)
      in
      if not (final_affine_ok && final_affine_res) then
        (loop, false)
      else
      let pol_mid = import_faithful_spol_or_fail midpoint_label pol mid_scop in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "mid-affine(schedule-only)" pol_mid;
      let artifact =
        tiling_artifact_from_scops_or_fail
          ~second_level:(Scheduler.second_level_tiling_enabled ())
          ~before_label:midpoint_label
          ~after_label:tiling_label
          mid_scop
          tiling_scop
      in
      let ws = PhaseTiling.convert_witness artifact.artifact_witness in
      let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "canonical-after" canonical_after;
      let pol_tiling_sched =
        import_schedule_only_spol_or_fail
          tiling_label
          canonical_after
          artifact.artifact_after_scop
      in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "after-tiled(schedule-only)" pol_tiling_sched;
      let pol_after_sched =
        if artifacts.phase_has_final_affine then
          import_schedule_only_spol_or_fail
            final_after_label
            pol_tiling_sched
            after_scop
        else
          pol_tiling_sched
      in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "after-final(schedule-only)" pol_after_sched;
      if debug_env_enabled "POLCERT_DEBUG_TILING_CODEGEN" then begin
        let raw_after =
          import_complete_spol_or_fail "after_tiled(raw)" artifact.artifact_after_scop
        in
        dump_poly_payload "after-tiled(raw)" raw_after
      end;
      let (pol_mid_val, pol_tiling_val) =
        normalize_stiling_validator_inputs pol_mid pol_tiling_sched
      in
      let pol_after = normalize_spol_codegen_input pol_after_sched in
      dump_poly_payload_if "POLCERT_DEBUG_TILING_CODEGEN" "after-tiled(used-for-codegen)" pol_after;
      let (res, ok) =
        checked_tiling_validate_with_bands pol_mid_val pol_tiling_val ws
      in
      if debug_env_enabled "POLCERT_DEBUG_TILING_CODEGEN" then
        Printf.eprintf
          "[debug-tiling-codegen] band-checked=%b(ok=%b)\n"
          res ok;
      if ok && res then
        SPolOpt.CoreOpt.Prepare.prepared_codegen
          (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
      else
        (loop, false)

let run_tiling_validator ~second_level before_file after_file =
  let report =
    PlutoTilingValidator.validate_files
      ~tiling_mode:(pluto_tiling_mode second_level)
      before_file
      after_file
  in
  print_endline (PlutoTilingValidator.render_report report);
  if report.ok then 0 else 2

let run_tiling_witness_extractor ~second_level before_file after_file =
  let witness =
    PlutoTilingValidator.extract_witness_from_files
      ~tiling_mode:(pluto_tiling_mode second_level)
      before_file
      after_file
  in
  print_endline (PlutoTilingValidator.render_witness witness);
  0

let nth_or_fail ctx xs n =
  try List.nth xs n
  with Failure _ ->
    frontend_failf "%s index %d is out of bounds" ctx n

let import_like_source_spol_or_fail label base scop =
  match SPolIRs.SPolIRs.PolyLang.from_openscop base scop with
  | Okk pol -> pol
  | Err msg ->
      frontend_failf
        "cannot import %s faithfully into syntax IR: %s"
        label
        (string_of_coq_err msg)

let apply_iss_bridge_to_spol_or_fail
    label
    before_pol
    (bridge : SLoopIss.parsed_iss_bridge) =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let ((before_pis, ctxt), vars) = before_pol in
  let stmt_ws = bridge.pib_witness.ISSWitness.iw_stmt_witnesses in
  if List.length before_pis <> List.length bridge.pib_before_domains then
    frontend_failf
      "%s: before stmt count mismatch between source polyhedral model (%d) and ISS bridge (%d)"
      label
      (List.length before_pis)
      (List.length bridge.pib_before_domains);
  if List.length stmt_ws <> List.length bridge.pib_after_domains then
    frontend_failf
      "%s: after stmt count mismatch between ISS witness (%d) and ISS bridge domains (%d)"
      label
      (List.length stmt_ws)
      (List.length bridge.pib_after_domains);
  let after_pis =
    List.map2
      (fun domain w ->
        let parent = int_of_nat w.ISSWitness.isw_parent_stmt in
        let source = nth_or_fail "ISS parent stmt" before_pis parent in
        { source with PL.pi_poly = domain })
      bridge.pib_after_domains
      stmt_ws
  in
  let after_pol = ((after_pis, ctxt), vars) in
  let ok =
    SPolOpt.CoreOpt.ValidatorCore.checked_iss_complete_cut_shape_validate
      before_pol
      after_pol
      bridge.pib_witness
  in
  if ok then
    after_pol
  else
    frontend_failf
      "%s: extracted ISS complete-cut-shape checker rejected reconstructed split program"
      label

let iss_bridge_from_scop_opt before_scop =
  match Scheduler.iss_identity_bridge_from_scop before_scop with
  | Okk text -> SLoopIss.parse_iss_bridge_text_opt text
  | Err msg ->
      frontend_failf "ISS bridge export failed: %s" (string_of_coq_err msg)

let run_iss_bridge_validator = SLoopIss.run_iss_bridge_validator
let run_iss_dump_validator = SLoopIss.run_iss_dump_validator
let run_iss_pluto_suite = SLoopIss.run_iss_pluto_suite
let run_iss_pluto_live_suite = SLoopIss.run_iss_pluto_live_suite

let optimize_identity_only loop =
  let pol = extract_strengthened_poly loop in
  SPolOpt.CoreOpt.Prepare.prepared_codegen (normalize_spol_codegen_input pol)

let optimize_affine_only loop =
  let pol = extract_strengthened_poly loop in
  SPolOpt.CoreOpt.affine_only_opt_prepared_from_poly pol

let profile_codegen_pipeline timings metrics pol =
  let ((pis, varctxt), vars) = pol in
  let es = List.length varctxt in
  let es_nat = nat_of_int es in
  let n = SPolOpt.CoreOpt.CodeGen.codegen_target_dim pol in
  let n_int = int_of_nat n in
  let k =
    List.fold_left
      max
      0
      (List.map
         (fun pi -> List.length (SPolIRs.SPolIRs.PolyLang.pi_schedule pi))
         pis)
  in
  let k_nat = nat_of_int k in
  let epis =
    time_stage timings "codegen_elim_schedule" (fun () ->
      SPolOpt.CoreOpt.CodeGen.PolyLang.elim_schedule k_nat es_nat pis)
  in
  let (polyloop, ok_generate) =
    time_stage timings "codegen_ast_generate" (fun () ->
      SPolOpt.CoreOpt.CodeGen.ASTGen.generate_loop_many
        (nat_of_int (n_int + k - es))
        (nat_of_int (n_int + k))
        epis)
  in
  let polyloop_stats = polyloop_stats_of_stmt polyloop in
  add_metric metrics "polyloop_raw.nodes" polyloop_stats.pl_nodes;
  add_metric metrics "polyloop_raw.loops" polyloop_stats.pl_loops;
  add_metric metrics "polyloop_raw.guards" polyloop_stats.pl_guards;
  add_metric metrics "polyloop_raw.instrs" polyloop_stats.pl_instrs;
  add_metric metrics "polyloop_raw.seqs" polyloop_stats.pl_seqs;
  add_metric metrics "polyloop_raw.constraints" polyloop_stats.pl_constraints;
  let (simp, ok_simplify) =
    time_stage timings "codegen_polyloop_simpl" (fun () ->
      SPolOpt.CoreOpt.CodeGen.PolyLoopSimplifier.polyloop_simplify polyloop es_nat [])
  in
  let simp_stats = polyloop_stats_of_stmt simp in
  add_metric metrics "polyloop_simpl.nodes" simp_stats.pl_nodes;
  add_metric metrics "polyloop_simpl.loops" simp_stats.pl_loops;
  add_metric metrics "polyloop_simpl.guards" simp_stats.pl_guards;
  add_metric metrics "polyloop_simpl.instrs" simp_stats.pl_instrs;
  add_metric metrics "polyloop_simpl.seqs" simp_stats.pl_seqs;
  add_metric metrics "polyloop_simpl.constraints" simp_stats.pl_constraints;
  let (loop_raw, ok_loopgen) =
    time_stage timings "codegen_loopgen" (fun () ->
      SPolOpt.CoreOpt.CodeGen.LoopGen.polyloop_to_loop es_nat simp)
  in
  let loop_stats = loop_stmt_stats loop_raw in
  add_metric metrics "loop_raw.nodes" loop_stats.loop_nodes;
  add_metric metrics "loop_raw.loops" loop_stats.loop_loops;
  add_metric metrics "loop_raw.guards" loop_stats.loop_guards;
  add_metric metrics "loop_raw.instrs" loop_stats.loop_instrs;
  add_metric metrics "loop_raw.seqs" loop_stats.loop_seqs;
  let loop_with_ctxt = ((loop_raw, varctxt), vars) in
  let loop_clean =
    time_stage timings "cleanup" (fun () ->
      SPolOpt.CoreOpt.Prepare.Cleanup.cleanup loop_with_ctxt)
  in
  (loop_clean, ok_generate && ok_simplify && ok_loopgen)

let profile_identity_only loop =
  let timings = ref [] in
  let metrics = ref [] in
  let pol0 = time_stage timings "extract" (fun () -> extract_poly loop) in
  let pol =
    time_stage timings "strengthen" (fun () ->
      SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0)
  in
  let pol_norm =
    time_stage timings "normalize_codegen" (fun () ->
      normalize_spol_codegen_input pol)
  in
  let pol_prep =
    time_stage timings "prepare_codegen" (fun () ->
      SPolOpt.CoreOpt.Prepare.prepare_codegen pol_norm)
  in
  let pol_codegen = maybe_dedup_spol_codegen_domains timings metrics pol_prep in
  let (loop_clean, ok_codegen) = profile_codegen_pipeline timings metrics pol_codegen in
  print_stage_timings !timings;
  print_profile_metrics !metrics;
  (loop_clean, ok_codegen)

let profile_affine_only loop =
  let timings = ref [] in
  let metrics = ref [] in
  let pol0 = time_stage timings "extract" (fun () -> extract_poly loop) in
  let pol =
    time_stage timings "strengthen" (fun () ->
      SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0)
  in
  let pol_mid = time_stage timings "affine_schedule" (fun () -> checked_affine_schedule_or_fail pol) in
  let pol_norm =
    time_stage timings "normalize_codegen" (fun () ->
      normalize_spol_codegen_input pol_mid)
  in
  let pol_prep =
    time_stage timings "prepare_codegen" (fun () ->
      SPolOpt.CoreOpt.Prepare.prepare_codegen pol_norm)
  in
  let pol_codegen = maybe_dedup_spol_codegen_domains timings metrics pol_prep in
  let (loop_clean, ok_codegen) = profile_codegen_pipeline timings metrics pol_codegen in
  print_stage_timings !timings;
  print_profile_metrics !metrics;
  (loop_clean, ok_codegen)

let profile_default_tiled loop =
  let timings = ref [] in
  let metrics = ref [] in
  let pol0 = time_stage timings "extract" (fun () -> extract_poly loop) in
  let pol =
    time_stage timings "strengthen" (fun () ->
      SPolOpt.CoreOpt.Strengthen.strengthen_pprog pol0)
  in
  let before_scop =
    time_stage timings "export_before_scop" (fun () -> poly_to_openscop pol)
  in
  let midpoint_label = current_midpoint_label () in
  let tiling_label = current_tiling_label () in
  let final_after_label = current_final_after_label () in
  let artifacts =
    time_stage timings "pluto_phase_pipeline" (fun () ->
      phase_pipeline_artifacts_or_fail before_scop)
  in
  let mid_scop = artifacts.phase_mid_scop in
  let tiling_scop = artifacts.phase_tiling_scop in
  let after_scop = artifacts.phase_after_scop in
  let pol_mid =
    time_stage timings "import_mid_affine" (fun () ->
      import_schedule_only_spol_or_fail midpoint_label pol mid_scop)
  in
  let (affine_res, affine_ok) =
    time_stage timings "affine_validate" (fun () ->
      affine_forward_scops "before" midpoint_label before_scop mid_scop)
  in
  if not (affine_ok && affine_res) then begin
    print_stage_timings !timings;
    print_profile_metrics !metrics;
    (loop, false)
  end else
    let artifact =
      time_stage timings "extract_tiling_artifact" (fun () ->
        tiling_artifact_from_scops_or_fail
          ~second_level:(Scheduler.second_level_tiling_enabled ())
          ~before_label:midpoint_label
          ~after_label:tiling_label
          mid_scop
          tiling_scop)
    in
    let ws =
      time_stage timings "convert_tiling_witness" (fun () ->
        PhaseTiling.convert_witness artifact.artifact_witness)
    in
    let canonical_after =
      time_stage timings "build_canonical_after" (fun () ->
        build_canonical_tiled_after_spol pol_mid ws)
    in
    let pol_tiling_sched =
      time_stage timings "import_after_schedule" (fun () ->
        import_schedule_only_spol_or_fail
          tiling_label
          canonical_after
          artifact.artifact_after_scop)
    in
    let final_affine_ok =
      if artifacts.phase_has_final_affine then
        let (res, ok) =
          time_stage timings "affine_validate_reschedule" (fun () ->
            affine_forward_scops tiling_label final_after_label tiling_scop after_scop)
        in
        ok && res
      else
        true
    in
    if not final_affine_ok then begin
      print_stage_timings !timings;
      print_profile_metrics !metrics;
      (loop, false)
    end else
    let pol_after_sched =
      if artifacts.phase_has_final_affine then
        time_stage timings "import_after_reschedule" (fun () ->
          import_schedule_only_spol_or_fail
            final_after_label
            pol_tiling_sched
            after_scop)
      else
        pol_tiling_sched
    in
    let (pol_mid_val, pol_tiling_val) =
      time_stage timings "normalize_tiling_inputs" (fun () ->
        normalize_stiling_validator_inputs pol_mid pol_tiling_sched)
    in
    let (res, ok) =
      time_stage timings "checked_tiling_validate" (fun () ->
        checked_tiling_validate_with_canonical pol_mid_val pol_tiling_val ws)
    in
    let pol_codegen =
      if ok && res then
        let pol_after_codegen =
          time_stage timings "current_view" (fun () ->
            SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after_sched)
        in
        time_stage timings "normalize_codegen" (fun () ->
          normalize_spol_codegen_input pol_after_codegen)
      else
        time_stage timings "normalize_codegen(fallback_affine)" (fun () ->
          normalize_spol_codegen_input pol_mid)
    in
    let pol_prep =
      time_stage timings "prepare_codegen" (fun () ->
        SPolOpt.CoreOpt.Prepare.prepare_codegen pol_codegen)
    in
    let pol_codegen = maybe_dedup_spol_codegen_domains timings metrics pol_prep in
    let (loop_clean, ok_codegen) = profile_codegen_pipeline timings metrics pol_codegen in
    print_stage_timings !timings;
    print_profile_metrics !metrics;
    (loop_clean, ok_codegen)

let profile_selected_optimization cfg loop =
  if cfg.force_parallel || cfg.force_parallel_strict || Option.is_some cfg.parallel_current_dim then
    frontend_failf "--profile-stages does not support parallel routes yet";
  if cfg.force_vector || cfg.force_vector_strict || Option.is_some cfg.vector_current_dim then
    frontend_failf "--profile-stages does not support vector routes yet";
  if cfg.force_iss then
    frontend_failf "--profile-stages currently supports the default no-ISS routes only";
  if cfg.force_second_level_tile then
    frontend_failf "--profile-stages does not support --second-level-tile yet";
  if cfg.force_identity then
    profile_identity_only loop
  else if cfg.force_notile then
    profile_affine_only loop
  else
    profile_default_tiled loop

let optimize_parallel_identity_only loop dim =
  let pol = extract_strengthened_poly loop in
  checked_parallel_current_codegen_or_fail "identity-parallel" pol dim

let optimize_parallel_affine_only loop dim =
  let pol = extract_strengthened_poly loop in
  let pol_mid = checked_affine_schedule_or_fail pol in
  checked_parallel_current_codegen_or_fail "affine-parallel" pol_mid dim

let optimize_parallel_iss_identity_only loop dim =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let pol_iss =
    match iss_bridge_from_scop_opt before_scop with
    | None -> pol
    | Some bridge ->
        apply_iss_bridge_to_spol_or_fail "iss-identity-parallel" pol bridge
  in
  checked_parallel_current_codegen_or_fail "iss-identity-parallel" pol_iss dim

let optimize_parallel_iss_affine_only loop dim =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let pol_iss =
    match iss_bridge_from_scop_opt before_scop with
    | None -> pol
    | Some bridge ->
        apply_iss_bridge_to_spol_or_fail "iss-affine-parallel" pol bridge
  in
  match Scheduler.affine_only_scop_scheduler_with_iss before_scop with
  | Err msg ->
      frontend_failf
        "iss-affine-parallel: Pluto affine scheduling failed: %s"
        (string_of_coq_err msg)
  | Okk mid_scop ->
      let pol_mid =
        import_like_source_spol_or_fail "mid_affine_iss_parallel" pol_iss mid_scop
      in
      let (affine_res, affine_ok) =
        SPolOpt.CoreOpt.validate pol_iss pol_mid
      in
      if not (affine_ok && affine_res) then
        frontend_failf
          "iss-affine-parallel: affine validation failed before manual parallel codegen";
      checked_parallel_current_codegen_or_fail "iss-affine-parallel" pol_mid dim

let optimize_parallel_phase_aligned loop dim =
  let pol = extract_strengthened_poly loop in
  let (before_scop, mid_scop, after_scop) = pluto_phase_scops loop in
  let (affine_res, affine_ok) =
    affine_forward_scops "before" "mid_affine" before_scop mid_scop
  in
  if not (affine_ok && affine_res) then
    frontend_failf
      "phase-parallel: affine validation failed before manual parallel codegen";
      let (tiling_res, tiling_ok) =
        tiling_forward_scops
          ~second_level:(Scheduler.second_level_tiling_enabled ())
          ~before_label:"mid_affine"
          ~after_label:"after_tiled"
          mid_scop
          after_scop
  in
  if not (tiling_ok && tiling_res) then
    frontend_failf
      "phase-parallel: tiling validation failed before manual parallel codegen";
  let pol_mid = import_faithful_spol_or_fail "mid_affine" pol mid_scop in
  let witness : PlutoTilingValidator.witness =
    PlutoTilingValidator.extract_witness_from_scops
      ~before_path:"mid_affine"
      ~after_path:"after_tiled"
      mid_scop
      after_scop
  in
  let ws = PhaseTiling.convert_witness witness in
  let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
  let pol_after_sched =
    import_schedule_only_spol_or_fail "after_tiled" canonical_after after_scop
  in
  let (pol_mid_val, pol_after_val) =
    normalize_stiling_validator_inputs pol_mid pol_after_sched
  in
  let pol_after = normalize_spol_codegen_input pol_after_val in
  let (res, ok) =
    checked_tiling_validate_with_canonical pol_mid_val pol_after_val ws
  in
  if not (ok && res) then
    frontend_failf
      "phase-parallel: checked tiling validation failed before manual parallel codegen";
  checked_parallel_current_codegen_or_fail "phase-parallel" pol_after dim

let optimize_parallel_iss_phase_aligned loop dim =
  match pluto_phase_scops_with_iss loop with
  | None ->
      frontend_failf "iss-phase-parallel: phase-aligned ISS Pluto pipeline failed"
  | Some (pol, before_scop, mid_scop, after_scop) ->
      let pol_iss =
        match iss_bridge_from_scop_opt before_scop with
        | None -> pol
        | Some bridge ->
            apply_iss_bridge_to_spol_or_fail "iss-phase-parallel" pol bridge
      in
      let (affine_res, affine_ok) =
        affine_forward_scops "before" "mid_affine_iss" before_scop mid_scop
      in
      if not (affine_ok && affine_res) then
        frontend_failf
          "iss-phase-parallel: affine validation failed before manual parallel codegen";
	      let (tiling_res, tiling_ok) =
	        tiling_forward_scops
	          ~second_level:(Scheduler.second_level_tiling_enabled ())
	          ~before_label:"mid_affine_iss"
	          ~after_label:"after_tiled"
	          mid_scop
	          after_scop
      in
      if not (tiling_ok && tiling_res) then
        frontend_failf
          "iss-phase-parallel: tiling validation failed before manual parallel codegen";
      let pol_mid =
        import_like_source_spol_or_fail "mid_affine_iss" pol_iss mid_scop
      in
      let witness : PlutoTilingValidator.witness =
        PlutoTilingValidator.extract_witness_from_scops
          ~before_path:"mid_affine_iss"
          ~after_path:"after_tiled"
          mid_scop
          after_scop
      in
      let ws = PhaseTiling.convert_witness witness in
      let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
      let pol_after_sched =
        import_schedule_only_spol_or_fail "after_tiled" canonical_after after_scop
      in
      let (pol_mid_val, pol_after_val) =
        normalize_stiling_validator_inputs pol_mid pol_after_sched
      in
      let pol_after = normalize_spol_codegen_input pol_after_val in
      let (res, ok) =
        checked_tiling_validate_with_canonical pol_mid_val pol_after_val ws
      in
      if not (ok && res) then
        frontend_failf
          "iss-phase-parallel: checked tiling validation failed before manual parallel codegen";
      checked_parallel_current_codegen_or_fail "iss-phase-parallel" pol_after dim

let optimize_affine_only_with_pluto_parallel_hint cfg loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.affine_only_scop_scheduler_with_parallel_hint before_scop with
  | Err _ ->
      (tag_loop_for_parallel_pretty loop, false)
  | Okk (mid_scop, hint) ->
      debug_parallel_hint_if "POLCERT_DEBUG_PARALLEL_HINT" hint;
      let pol_mid =
        import_like_source_spol_or_fail "mid_affine_parallel" pol mid_scop
      in
      let (affine_res, affine_ok) =
        SPolOpt.CoreOpt.validate pol pol_mid
      in
      if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
        Printf.eprintf
          "[debug-parallel] affine-only validate=%b(ok=%b)\n"
          affine_res affine_ok;
      debug_parallel_dim_scan_if "POLCERT_DEBUG_PARALLEL_HINT" pol_mid;
      if not (affine_ok && affine_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
        let hinted_dims = hint_dims hint in
        let try_codegen =
          if cfg.force_multipar then
            try_pluto_multipar_codegen pol_mid hinted_dims cfg.force_parallel_strict
          else
            try_pluto_parallel_codegen
              pol_mid
              (first_hint_dim hint)
              cfg.force_parallel_strict
        in
        begin match try_codegen with
        | Some (pl, used_hint) -> (pl, used_hint)
        | None ->
            let (fallback, _ok) = tagged_prepared_codegen pol_mid in
            (fallback, false)
        end

let optimize_identity_tiled_with_pluto_parallel_hint cfg loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.tile_only_scop_scheduler_with_parallel_hint before_scop with
  | Err _ ->
      (tag_loop_for_parallel_pretty loop, false)
  | Okk (after_scop, hint) ->
      debug_parallel_hint_if "POLCERT_DEBUG_PARALLEL_HINT" hint;
      let (tiling_res, tiling_ok) =
        tiling_forward_scops
          ~second_level:false
          ~before_label:"identity_before"
          ~after_label:"identity_tiled"
          before_scop
          after_scop
      in
      if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
        Printf.eprintf
          "[debug-parallel] identity tiled validate=%b(ok=%b)\n"
          tiling_res tiling_ok;
      if not (tiling_ok && tiling_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
        let artifact =
          tiling_artifact_from_scops_or_fail
            ~second_level:false
            ~before_label:"identity_before"
            ~after_label:"identity_tiled"
            before_scop
            after_scop
        in
        let ws = PhaseTiling.convert_witness artifact.artifact_witness in
        let canonical_after = build_canonical_tiled_after_spol pol ws in
        let pol_after_sched =
          import_schedule_only_spol_or_fail
            "identity_tiled"
            canonical_after
            artifact.artifact_after_scop
        in
        let (pol_before_val, pol_after_val) =
          normalize_stiling_validator_inputs pol pol_after_sched
        in
        let pol_after = normalize_spol_codegen_input pol_after_val in
        let (res, ok) =
          checked_tiling_validate_with_canonical
            pol_before_val
            pol_after_val
            ws
        in
        if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
          Printf.eprintf
            "[debug-parallel] identity checked_tiling_validate=%b(ok=%b)\n"
            res ok;
        debug_parallel_dim_scan_if "POLCERT_DEBUG_PARALLEL_HINT" pol_after;
        if not (ok && res) then
          (tag_loop_for_parallel_pretty loop, false)
        else
          let hinted_dims = hint_dims hint in
          let try_codegen =
            if cfg.force_multipar then
              try_pluto_multipar_codegen pol_after hinted_dims cfg.force_parallel_strict
            else
              try_pluto_parallel_codegen
                pol_after
                (first_hint_dim hint)
                cfg.force_parallel_strict
          in
          begin match try_codegen with
          | Some (pl, used_hint) -> (pl, used_hint)
          | None ->
              let (fallback, _ok) =
                tagged_prepared_codegen
                  (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
              in
              (fallback, false)
          end

let optimize_with_iss_affine_parallel_hint cfg loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let pol_iss =
    match iss_bridge_from_scop_opt before_scop with
    | None -> pol
    | Some bridge ->
        apply_iss_bridge_to_spol_or_fail "iss-affine-parallel" pol bridge
  in
  match Scheduler.affine_only_scop_scheduler_with_iss_with_parallel_hint before_scop with
  | Err _ ->
      (tag_loop_for_parallel_pretty loop, false)
  | Okk (mid_scop, hint) ->
      debug_parallel_hint_if "POLCERT_DEBUG_PARALLEL_HINT" hint;
      let pol_mid =
        import_like_source_spol_or_fail "mid_affine_iss_parallel" pol_iss mid_scop
      in
      let (affine_res, affine_ok) =
        SPolOpt.CoreOpt.validate pol_iss pol_mid
      in
      if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
        Printf.eprintf
          "[debug-parallel] iss affine-only validate=%b(ok=%b)\n"
          affine_res affine_ok;
      debug_parallel_dim_scan_if "POLCERT_DEBUG_PARALLEL_HINT" pol_mid;
      if not (affine_ok && affine_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
        let hinted_dims = hint_dims hint in
        let try_codegen =
          if cfg.force_multipar then
            try_pluto_multipar_codegen pol_mid hinted_dims cfg.force_parallel_strict
          else
            try_pluto_parallel_codegen
              pol_mid
              (first_hint_dim hint)
              cfg.force_parallel_strict
        in
        begin match try_codegen with
        | Some (pl, used_hint) -> (pl, used_hint)
        | None ->
            let (fallback, _ok) = tagged_prepared_codegen pol_mid in
            (fallback, false)
        end

let optimize_with_diamond_parallel_hint cfg loop =
  let hint = pluto_diamond_parallel_hint cfg loop in
  debug_parallel_hint_if "POLCERT_DEBUG_PARALLEL_HINT" hint;
  let try_codegen =
    if cfg.force_multipar then
      try_diamond_multipar_codegen
        cfg.force_iss
        loop
        (hint_dims hint)
        cfg.force_parallel_strict
    else
      try_diamond_parallel_codegen
        cfg.force_iss
        loop
        (first_hint_dim hint)
        cfg.force_parallel_strict
  in
  match try_codegen
  with
  | Some (pl, used_hint) -> (pl, used_hint)
  | None -> (tag_loop_for_parallel_pretty loop, false)

let optimize_with_iss_identity loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let pol_iss =
    match iss_bridge_from_scop_opt before_scop with
    | None -> pol
    | Some bridge ->
        apply_iss_bridge_to_spol_or_fail "iss-identity" pol bridge
  in
  SPolOpt.CoreOpt.Prepare.prepared_codegen
    (normalize_spol_codegen_input pol_iss)

let optimize_with_iss_affine loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let pol_iss =
    match iss_bridge_from_scop_opt before_scop with
    | None -> pol
    | Some bridge ->
        apply_iss_bridge_to_spol_or_fail "iss-affine" pol bridge
  in
  match Scheduler.affine_only_scop_scheduler_with_iss before_scop with
  | Err _ -> (loop, false)
  | Okk mid_scop ->
      let pol_mid = import_like_source_spol_or_fail "mid_affine_iss" pol_iss mid_scop in
      let (affine_res, affine_ok) =
        SPolOpt.CoreOpt.validate pol_iss pol_mid
      in
      if affine_ok && affine_res then
        SPolOpt.CoreOpt.Prepare.prepared_codegen
          (normalize_spol_codegen_input pol_mid)
      else
        (loop, false)

let optimize_with_iss_phase_aligned_pluto loop =
  match pluto_phase_scops_with_iss loop with
  | None -> (loop, false)
  | Some (pol, before_scop, mid_scop, after_scop) ->
      let pol_iss =
        match iss_bridge_from_scop_opt before_scop with
        | None -> pol
        | Some bridge ->
            apply_iss_bridge_to_spol_or_fail "iss-phase" pol bridge
      in
      let pol_mid = import_like_source_spol_or_fail "mid_affine_iss" pol_iss mid_scop in
      let (affine_res, affine_ok) =
        SPolOpt.CoreOpt.validate pol_iss pol_mid
      in
      if not (affine_ok && affine_res) then
        (loop, false)
      else
	        let (tiling_res, tiling_ok) =
	          tiling_forward_scops
	            ~second_level:(Scheduler.second_level_tiling_enabled ())
	            ~before_label:"mid_affine_iss"
	            ~after_label:"after_tiled"
	            mid_scop
	            after_scop
        in
        if not (tiling_ok && tiling_res) then
          (loop, false)
	        else
	          let artifact =
	            tiling_artifact_from_scops_or_fail
	              ~second_level:(Scheduler.second_level_tiling_enabled ())
	              ~before_label:"mid_affine_iss"
	              ~after_label:"after_tiled"
	              mid_scop
	              after_scop
	          in
	          let ws = PhaseTiling.convert_witness artifact.artifact_witness in
	          let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
	          let pol_after_sched =
	            import_schedule_only_spol_or_fail
	              "after_tiled"
	              canonical_after
	              artifact.artifact_after_scop
	          in
          let pol_after = normalize_spol_codegen_input pol_after_sched in
          let (res, ok) =
            checked_tiling_validate_with_canonical pol_mid pol_after ws
          in
          if ok && res then
            SPolOpt.CoreOpt.Prepare.prepared_codegen
              (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
          else
            (loop, false)

let optimize_with_phase_aligned_pluto_parallel_hint cfg loop =
  match pluto_phase_scops_with_parallel_hint loop with
  | None -> (tag_loop_for_parallel_pretty loop, false)
  | Some (pol, before_scop, mid_scop, after_scop, hint) ->
      debug_parallel_hint_if "POLCERT_DEBUG_PARALLEL_HINT" hint;
      let (affine_res, affine_ok) =
        affine_forward_scops "before" "mid_affine" before_scop mid_scop
      in
      if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
        Printf.eprintf
          "[debug-parallel] phase affine validate=%b(ok=%b)\n"
          affine_res affine_ok;
      if not (affine_ok && affine_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
      let (tiling_res, tiling_ok) =
        tiling_forward_scops
          ~second_level:cfg.force_second_level_tile
          ~before_label:"mid_affine"
          ~after_label:"after_tiled"
          mid_scop
          after_scop
        in
        if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
          Printf.eprintf
            "[debug-parallel] phase tiling validate=%b(ok=%b)\n"
            tiling_res tiling_ok;
        if not (tiling_ok && tiling_res) then
          (tag_loop_for_parallel_pretty loop, false)
        else
          let pol_mid = import_faithful_spol_or_fail "mid_affine" pol mid_scop in
          let artifact =
            tiling_artifact_from_scops_or_fail
              ~second_level:cfg.force_second_level_tile
              ~before_label:"mid_affine"
              ~after_label:"after_tiled"
              mid_scop
              after_scop
          in
          let ws = PhaseTiling.convert_witness artifact.artifact_witness in
          let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
          let pol_after_sched =
            import_schedule_only_spol_or_fail
              "after_tiled"
              canonical_after
              artifact.artifact_after_scop
          in
          let (pol_mid_val, pol_after_val) =
            normalize_stiling_validator_inputs pol_mid pol_after_sched
          in
          let pol_after = normalize_spol_codegen_input pol_after_val in
          let (res, ok) =
            checked_tiling_validate_with_canonical pol_mid_val pol_after_val ws
          in
          if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
            Printf.eprintf
              "[debug-parallel] checked_tiling_validate=%b(ok=%b)\n"
              res ok;
          debug_parallel_dim_scan_if "POLCERT_DEBUG_PARALLEL_HINT" pol_after;
          if not (ok && res) then
            (tag_loop_for_parallel_pretty loop, false)
          else
            let hinted_dims = hint_dims hint in
            let try_codegen =
              if cfg.force_multipar then
                try_pluto_multipar_codegen pol_after hinted_dims cfg.force_parallel_strict
              else
                try_pluto_parallel_codegen
                  pol_after
                  (first_hint_dim hint)
                  cfg.force_parallel_strict
            in
            begin
              match try_codegen with
              | Some (pl, used_hint) -> (pl, used_hint)
              | None ->
                  let (fallback, _ok) =
                    tagged_prepared_codegen
                      (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
                  in
                  (fallback, false)
            end

let optimize_with_iss_phase_aligned_pluto_parallel_hint cfg loop =
  match pluto_phase_scops_with_iss_and_parallel_hint loop with
  | None -> (tag_loop_for_parallel_pretty loop, false)
  | Some (pol, before_scop, mid_scop, after_scop, hint) ->
      debug_parallel_hint_if "POLCERT_DEBUG_PARALLEL_HINT" hint;
      let pol_iss =
        match iss_bridge_from_scop_opt before_scop with
        | None -> pol
        | Some bridge ->
            apply_iss_bridge_to_spol_or_fail "iss-phase-parallel" pol bridge
      in
      let (affine_res, affine_ok) =
        affine_forward_scops "before" "mid_affine_iss" before_scop mid_scop
      in
      if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
        Printf.eprintf
          "[debug-parallel] iss phase affine validate=%b(ok=%b)\n"
          affine_res affine_ok;
      if not (affine_ok && affine_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
      let (tiling_res, tiling_ok) =
        tiling_forward_scops
          ~second_level:cfg.force_second_level_tile
          ~before_label:"mid_affine_iss"
          ~after_label:"after_tiled"
          mid_scop
          after_scop
        in
        if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
          Printf.eprintf
            "[debug-parallel] iss phase tiling validate=%b(ok=%b)\n"
            tiling_res tiling_ok;
        if not (tiling_ok && tiling_res) then
          (tag_loop_for_parallel_pretty loop, false)
        else
          let pol_mid =
            import_like_source_spol_or_fail "mid_affine_iss" pol_iss mid_scop
          in
          let artifact =
            tiling_artifact_from_scops_or_fail
              ~second_level:cfg.force_second_level_tile
              ~before_label:"mid_affine_iss"
              ~after_label:"after_tiled"
              mid_scop
              after_scop
          in
          let ws = PhaseTiling.convert_witness artifact.artifact_witness in
          let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
          let pol_after_sched =
            import_schedule_only_spol_or_fail
              "after_tiled"
              canonical_after
              artifact.artifact_after_scop
          in
          let (pol_mid_val, pol_after_val) =
            normalize_stiling_validator_inputs pol_mid pol_after_sched
          in
          let pol_after = normalize_spol_codegen_input pol_after_val in
          let (res, ok) =
            checked_tiling_validate_with_canonical pol_mid_val pol_after_val ws
          in
          if debug_env_enabled "POLCERT_DEBUG_PARALLEL_HINT" then
            Printf.eprintf
              "[debug-parallel] iss checked_tiling_validate=%b(ok=%b)\n"
              res ok;
          debug_parallel_dim_scan_if "POLCERT_DEBUG_PARALLEL_HINT" pol_after;
          if not (ok && res) then
            (tag_loop_for_parallel_pretty loop, false)
          else
            let hinted_dims = hint_dims hint in
            let try_codegen =
              if cfg.force_multipar then
                try_pluto_multipar_codegen pol_after hinted_dims cfg.force_parallel_strict
              else
                try_pluto_parallel_codegen
                  pol_after
                  (first_hint_dim hint)
                  cfg.force_parallel_strict
            in
            begin
              match try_codegen with
              | Some (pl, used_hint) -> (pl, used_hint)
              | None ->
                  let (fallback, _ok) =
                    tagged_prepared_codegen
                      (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
                  in
                  (fallback, false)
            end

let optimize_affine_only_with_pluto_vector_hint cfg loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.affine_only_scop_scheduler_with_vector_hint before_scop with
  | Err _ ->
      (tag_loop_for_parallel_pretty loop, false)
  | Okk (mid_scop, hint) ->
      debug_vector_hint_if "POLCERT_DEBUG_VECTOR_HINT" hint;
      let pol_mid =
        import_like_source_spol_or_fail "mid_affine_vector" pol mid_scop
      in
      let (affine_res, affine_ok) =
        SPolOpt.CoreOpt.validate pol pol_mid
      in
      if not (affine_ok && affine_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
        begin match try_pluto_vector_codegen
                      pol_mid
                      (first_hint_dim hint)
                      cfg.force_vector_strict with
        | Some (pl, used_hint) -> (pl, used_hint)
        | None ->
            let (fallback, _ok) = tagged_prepared_codegen pol_mid in
            (fallback, false)
        end

let optimize_identity_tiled_with_pluto_vector_hint cfg loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  match Scheduler.tile_only_scop_scheduler_with_vector_hint before_scop with
  | Err _ ->
      (tag_loop_for_parallel_pretty loop, false)
  | Okk (after_scop, hint) ->
      debug_vector_hint_if "POLCERT_DEBUG_VECTOR_HINT" hint;
      let (tiling_res, tiling_ok) =
        tiling_forward_scops
          ~second_level:false
          ~before_label:"identity_before"
          ~after_label:"identity_tiled"
          before_scop
          after_scop
      in
      if not (tiling_ok && tiling_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
        let artifact =
          tiling_artifact_from_scops_or_fail
            ~second_level:false
            ~before_label:"identity_before"
            ~after_label:"identity_tiled"
            before_scop
            after_scop
        in
        let ws = PhaseTiling.convert_witness artifact.artifact_witness in
        let canonical_after = build_canonical_tiled_after_spol pol ws in
        let pol_after_sched =
          import_schedule_only_spol_or_fail
            "identity_tiled"
            canonical_after
            artifact.artifact_after_scop
        in
        let (pol_before_val, pol_after_val) =
          normalize_stiling_validator_inputs pol pol_after_sched
        in
        let pol_after = normalize_spol_codegen_input pol_after_val in
        let (res, ok) =
          checked_tiling_validate_with_canonical
            pol_before_val
            pol_after_val
            ws
        in
        if not (ok && res) then
          (tag_loop_for_parallel_pretty loop, false)
        else
          begin match try_pluto_vector_codegen
                        pol_after
                        (first_hint_dim hint)
                        cfg.force_vector_strict with
          | Some (pl, used_hint) -> (pl, used_hint)
          | None ->
              let (fallback, _ok) =
                tagged_prepared_codegen
                  (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
              in
              (fallback, false)
          end

let optimize_with_iss_affine_vector_hint cfg loop =
  let pol = extract_strengthened_poly loop in
  let before_scop = poly_to_openscop pol in
  let pol_iss =
    match iss_bridge_from_scop_opt before_scop with
    | None -> pol
    | Some bridge ->
        apply_iss_bridge_to_spol_or_fail "iss-affine-vector" pol bridge
  in
  match Scheduler.affine_only_scop_scheduler_with_iss_with_vector_hint before_scop with
  | Err _ ->
      (tag_loop_for_parallel_pretty loop, false)
  | Okk (mid_scop, hint) ->
      debug_vector_hint_if "POLCERT_DEBUG_VECTOR_HINT" hint;
      let pol_mid =
        import_like_source_spol_or_fail "mid_affine_iss_vector" pol_iss mid_scop
      in
      let (affine_res, affine_ok) =
        SPolOpt.CoreOpt.validate pol_iss pol_mid
      in
      if not (affine_ok && affine_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
        begin match try_pluto_vector_codegen
                      pol_mid
                      (first_hint_dim hint)
                      cfg.force_vector_strict with
        | Some (pl, used_hint) -> (pl, used_hint)
        | None ->
            let (fallback, _ok) = tagged_prepared_codegen pol_mid in
            (fallback, false)
        end

let optimize_with_diamond_vector_hint cfg loop =
  let hint = pluto_diamond_vector_hint cfg loop in
  debug_vector_hint_if "POLCERT_DEBUG_VECTOR_HINT" hint;
  match try_diamond_vector_codegen
          cfg.force_iss
          loop
          (first_hint_dim hint)
          cfg.force_vector_strict
  with
  | Some (pl, used_hint) -> (pl, used_hint)
  | None -> (tag_loop_for_parallel_pretty loop, false)

let optimize_with_phase_aligned_pluto_vector_hint cfg loop =
  match pluto_phase_scops_with_vector_hint loop with
  | None -> (tag_loop_for_parallel_pretty loop, false)
  | Some (pol, before_scop, mid_scop, after_scop, hint) ->
      debug_vector_hint_if "POLCERT_DEBUG_VECTOR_HINT" hint;
      let (affine_res, affine_ok) =
        affine_forward_scops "before" "mid_affine" before_scop mid_scop
      in
      if not (affine_ok && affine_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
        let (tiling_res, tiling_ok) =
          tiling_forward_scops
            ~second_level:cfg.force_second_level_tile
            ~before_label:"mid_affine"
            ~after_label:"after_tiled"
            mid_scop
            after_scop
        in
        if not (tiling_ok && tiling_res) then
          (tag_loop_for_parallel_pretty loop, false)
        else
          let pol_mid = import_faithful_spol_or_fail "mid_affine" pol mid_scop in
          let artifact =
            tiling_artifact_from_scops_or_fail
              ~second_level:cfg.force_second_level_tile
              ~before_label:"mid_affine"
              ~after_label:"after_tiled"
              mid_scop
              after_scop
          in
          let ws = PhaseTiling.convert_witness artifact.artifact_witness in
          let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
          let pol_after_sched =
            import_schedule_only_spol_or_fail
              "after_tiled"
              canonical_after
              artifact.artifact_after_scop
          in
          let (pol_mid_val, pol_after_val) =
            normalize_stiling_validator_inputs pol_mid pol_after_sched
          in
          let pol_after = normalize_spol_codegen_input pol_after_val in
          let (res, ok) =
            checked_tiling_validate_with_canonical pol_mid_val pol_after_val ws
          in
          if not (ok && res) then
            (tag_loop_for_parallel_pretty loop, false)
          else
            begin match try_pluto_vector_codegen
                          pol_after
                          (first_hint_dim hint)
                          cfg.force_vector_strict with
            | Some (pl, used_hint) -> (pl, used_hint)
            | None ->
                let (fallback, _ok) =
                  tagged_prepared_codegen
                    (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
                in
                (fallback, false)
            end

let optimize_with_iss_phase_aligned_pluto_vector_hint cfg loop =
  match pluto_phase_scops_with_iss_and_vector_hint loop with
  | None -> (tag_loop_for_parallel_pretty loop, false)
  | Some (pol, before_scop, mid_scop, after_scop, hint) ->
      debug_vector_hint_if "POLCERT_DEBUG_VECTOR_HINT" hint;
      let pol_iss =
        match iss_bridge_from_scop_opt before_scop with
        | None -> pol
        | Some bridge ->
            apply_iss_bridge_to_spol_or_fail "iss-phase-vector" pol bridge
      in
      let (affine_res, affine_ok) =
        affine_forward_scops "before" "mid_affine_iss" before_scop mid_scop
      in
      if not (affine_ok && affine_res) then
        (tag_loop_for_parallel_pretty loop, false)
      else
        let (tiling_res, tiling_ok) =
          tiling_forward_scops
            ~second_level:cfg.force_second_level_tile
            ~before_label:"mid_affine_iss"
            ~after_label:"after_tiled"
            mid_scop
            after_scop
        in
        if not (tiling_ok && tiling_res) then
          (tag_loop_for_parallel_pretty loop, false)
        else
          let pol_mid =
            import_like_source_spol_or_fail "mid_affine_iss" pol_iss mid_scop
          in
          let artifact =
            tiling_artifact_from_scops_or_fail
              ~second_level:cfg.force_second_level_tile
              ~before_label:"mid_affine_iss"
              ~after_label:"after_tiled"
              mid_scop
              after_scop
          in
          let ws = PhaseTiling.convert_witness artifact.artifact_witness in
          let canonical_after = build_canonical_tiled_after_spol pol_mid ws in
          let pol_after_sched =
            import_schedule_only_spol_or_fail
              "after_tiled"
              canonical_after
              artifact.artifact_after_scop
          in
          let (pol_mid_val, pol_after_val) =
            normalize_stiling_validator_inputs pol_mid pol_after_sched
          in
          let pol_after = normalize_spol_codegen_input pol_after_val in
          let (res, ok) =
            checked_tiling_validate_with_canonical pol_mid_val pol_after_val ws
          in
          if not (ok && res) then
            (tag_loop_for_parallel_pretty loop, false)
          else
            begin match try_pluto_vector_codegen
                          pol_after
                          (first_hint_dim hint)
                          cfg.force_vector_strict with
            | Some (pl, used_hint) -> (pl, used_hint)
            | None ->
                let (fallback, _ok) =
                  tagged_prepared_codegen
                    (SPolIRs.SPolIRs.PolyLang.current_view_pprog pol_after)
                in
                (fallback, false)
            end

let standalone_handlers = {
  sa_run_affine_validator = run_affine_validator;
  sa_run_tiling_witness_extractor = run_tiling_witness_extractor;
  sa_run_tiling_validator = run_tiling_validator;
  sa_run_iss_dump_validator = run_iss_dump_validator;
  sa_run_iss_bridge_validator = run_iss_bridge_validator;
  sa_run_iss_pluto_suite = run_iss_pluto_suite;
  sa_run_iss_pluto_live_suite = run_iss_pluto_live_suite;
}

let optimize_identity_tiled loop =
  if Scheduler.second_level_tiling_enabled () then
    SPolOpt.opt_identity_tiled_generic loop
  else
    SBandTilingOpt.opt_identity_tiled loop

let optimize_iss_identity_tiled loop =
  if Scheduler.second_level_tiling_enabled () then
    SPolOpt.opt_identity_tiled_generic_with_iss loop
  else
    SBandTilingOpt.opt_identity_tiled_with_iss loop

let sequential_handlers = {
  seq_optimize_diamond = SBandTilingOpt.opt_diamond;
  seq_optimize_diamond_iss = SBandTilingOpt.opt_diamond_with_iss;
  seq_optimize_iss_identity_tiled = optimize_iss_identity_tiled;
  seq_optimize_iss_identity = optimize_with_iss_identity;
  seq_optimize_iss_affine = optimize_with_iss_affine;
  seq_optimize_iss_default = SPolOpt.opt_with_iss;
  seq_optimize_identity = SPolOpt.opt_identity;
  seq_optimize_identity_tiled = optimize_identity_tiled;
  seq_optimize_affine = SPolOpt.opt_affine;
  seq_optimize_legacy = SPolOpt.opt;
  seq_optimize_default = SBandTilingOpt.opt;
}

let hinted_parallel_handlers = {
  hint_optimize_diamond = optimize_with_diamond_parallel_hint;
  hint_optimize_identity_tiled = optimize_identity_tiled_with_pluto_parallel_hint;
  hint_optimize_iss_affine = optimize_with_iss_affine_parallel_hint;
  hint_optimize_iss_default = optimize_with_iss_phase_aligned_pluto_parallel_hint;
  hint_optimize_affine = optimize_affine_only_with_pluto_parallel_hint;
  hint_optimize_default = optimize_with_phase_aligned_pluto_parallel_hint;
}

let hinted_vector_handlers = {
  hint_optimize_diamond = optimize_with_diamond_vector_hint;
  hint_optimize_identity_tiled = optimize_identity_tiled_with_pluto_vector_hint;
  hint_optimize_iss_affine = optimize_with_iss_affine_vector_hint;
  hint_optimize_iss_default = optimize_with_iss_phase_aligned_pluto_vector_hint;
  hint_optimize_affine = optimize_affine_only_with_pluto_vector_hint;
  hint_optimize_default = optimize_with_phase_aligned_pluto_vector_hint;
}

let current_parallel_handlers = {
  cur_optimize_diamond = SParallelPolOpt.opt_parallel_current_diamond;
  cur_optimize_diamond_iss = SParallelPolOpt.opt_parallel_current_diamond_with_iss;
  cur_optimize_identity_tiled = SParallelPolOpt.opt_parallel_current_identity_tiled;
  cur_optimize_iss_identity = SParallelPolOpt.opt_parallel_current_identity_with_iss;
  cur_optimize_iss_affine = SParallelPolOpt.opt_parallel_current_affine_with_iss;
  cur_optimize_iss_default = SParallelPolOpt.opt_parallel_current_with_iss;
  cur_optimize_identity = SParallelPolOpt.opt_parallel_current_identity;
  cur_optimize_affine = SParallelPolOpt.opt_parallel_current_affine;
  cur_optimize_default = SParallelPolOpt.opt_parallel_current;
}

let current_vector_handlers = {
  cur_optimize_diamond = SParallelPolOpt.opt_vector_current_diamond;
  cur_optimize_diamond_iss = SParallelPolOpt.opt_vector_current_diamond_with_iss;
  cur_optimize_identity_tiled = SParallelPolOpt.opt_vector_current_identity_tiled;
  cur_optimize_iss_identity = SParallelPolOpt.opt_vector_current_identity_with_iss;
  cur_optimize_iss_affine = SParallelPolOpt.opt_vector_current_affine_with_iss;
  cur_optimize_iss_default = SParallelPolOpt.opt_vector_current_with_iss;
  cur_optimize_identity = SParallelPolOpt.opt_vector_current_identity;
  cur_optimize_affine = SParallelPolOpt.opt_vector_current_affine;
  cur_optimize_default = SParallelPolOpt.opt_vector_current;
}

let run_selected_optimization cfg loop =
  SLoopDispatch.run_selected_optimization cfg sequential_handlers loop

let run_selected_parallel_optimization cfg loop =
  SLoopDispatch.run_selected_parallel_optimization
    cfg
    hinted_parallel_handlers
    loop

let run_selected_vector_optimization cfg loop =
  SLoopDispatch.run_selected_parallel_optimization
    cfg
    hinted_vector_handlers
    loop

let run_selected_parallel_current_optimization cfg loop dim =
  SLoopDispatch.run_selected_parallel_current_optimization
    cfg
    current_parallel_handlers
    loop
    dim

let run_selected_vector_current_optimization cfg loop dim =
  SLoopDispatch.run_selected_parallel_current_optimization
    cfg
    current_vector_handlers
    loop
    dim

let pluto_unroll_factor cfg =
  match pluto_extra_value "--ufactor=" cfg with
  | Some value ->
      begin
        try max 1 (int_of_string value)
        with Failure _ -> 8
      end
  | None -> 8

let checked_unrolljam_fusion_guard loop fuel =
  let plan : SLoopJamValidator.CoreLoopJamValidator.JamCore.jam_plan =
    {
      SLoopJamValidator.CoreLoopJamValidator.JamCore.jam_outer_dim = nat_of_int 0;
      jam_factor = fuel;
    }
  in
  let (cert_res, cert_ok) =
    SLoopJamValidator.checked_loop_jam_current loop plan
  in
  cert_ok &&
  match cert_res with
  | Okk _ -> true
  | Err _ -> false

let apply_const_unroll_postpass cfg loop =
  if cfg.force_const_unroll then begin
    let cleanup_loop loop =
      SPolOpt.CoreOpt.Prepare.Cleanup.cleanup loop
    in
    let const_changed = SLoopUnroll.const_unroll_changed loop in
    let loop =
      if const_changed then cleanup_loop (SLoopUnroll.const_unroll loop) else loop
    in
    if cfg.pluto_unrolljam_seen then begin
      let fuel = nat_of_int (pluto_unroll_factor cfg) in
      if SLoopUnroll.block_unroll_changed fuel loop then
        let block_unrolled = cleanup_loop (SLoopUnroll.block_unroll fuel loop) in
        if checked_unrolljam_fusion_guard loop fuel then
          cleanup_loop (SLoopJamLower.unrolljam_loop fuel loop)
        else
          block_unrolled
      else if const_changed then
        loop
      else
        frontend_failf
          "--unrolljam could not find a sequential Loop IR loop to block-unroll";
    end
    else if const_changed then
      loop
    else
      frontend_failf
        "--const-unroll currently applies only when the final sequential Loop IR contains a statically constant-bounded loop"
  end
  else
    loop

let () =
  try
    Gc.set { (Gc.get()) with
               Gc.minor_heap_size = 524288;
               Gc.major_heap_increment = 4194304 };
    let cfg = parse_args () in
    validate_flag_model Sys.argv.(0) cfg;
    if cfg.pluto_compat_dry_run then exit 0;
    configure_scheduler_modes cfg;
    match SLoopDispatch.run_standalone_action cfg standalone_handlers with
    | ExitCode code ->
        exit code
    | ContinueToLoop ->
      begin match cfg.input with
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
        if cfg.profile_stages then begin
          let (optimized, ok) = profile_selected_optimization cfg loop in
          let optimized = apply_const_unroll_postpass cfg optimized in
          if not ok then prerr_endline "[alarm] optimization triggered a checked fallback or warning";
          print_section "Optimized Loop" (SLoopPretty.string_of_loop optimized);
          exit 0
        end;
        if cfg.dump_extracted_openscop then dump_extracted_openscop loop;
        if cfg.dump_scheduled_openscop then
          if cfg.force_vector then
            dump_scheduled_openscop_with_vector cfg loop
          else if cfg.force_parallel then
            dump_scheduled_openscop_with_parallel cfg loop
          else
            dump_scheduled_openscop loop;
        if cfg.debug_scheduler then debug_scheduler loop;
        if debug_env_enabled "POLCERT_DEBUG_GENERIC_TILING" then
          debug_generic_tiling_runtime loop;
        if debug_env_enabled "POLCERT_DEBUG_BAND_TILING" then
          debug_band_tiling_runtime loop;
        begin match cfg.vector_current_dim, cfg.parallel_current_dim with
        | Some dim, _ ->
            let (optimized, ok) =
              run_selected_vector_current_optimization cfg loop dim
            in
            if not ok then prerr_endline "[alarm] optimization triggered a checked fallback or warning";
            print_section "Optimized Loop" (string_of_parallel_loop optimized)
        | None, Some dim ->
            let (optimized, ok) =
              run_selected_parallel_current_optimization cfg loop dim
            in
            if not ok then prerr_endline "[alarm] optimization triggered a checked fallback or warning";
            print_section "Optimized Loop" (string_of_parallel_loop optimized)
        | None, None ->
            if cfg.force_vector then
              let (optimized, ok) = run_selected_vector_optimization cfg loop in
              if not ok then prerr_endline "[alarm] optimization triggered a checked fallback or warning";
              print_section "Optimized Loop" (string_of_parallel_loop optimized)
            else if cfg.force_parallel then
              let (optimized, ok) = run_selected_parallel_optimization cfg loop in
              if not ok then prerr_endline "[alarm] optimization triggered a checked fallback or warning";
              print_section "Optimized Loop" (string_of_parallel_loop optimized)
            else
              let (optimized, ok) = run_selected_optimization cfg loop in
              let optimized = apply_const_unroll_postpass cfg optimized in
              if not ok then prerr_endline "[alarm] optimization triggered a checked fallback or warning";
              print_section "Optimized Loop" (SLoopPretty.string_of_loop optimized)
        end
      end
    | InvalidStandaloneFlags ->
        prerr_endline (usage Sys.argv.(0));
        exit 2
  with
  | Sys_error msg -> error no_loc "%s" msg; exit 2
  | SLoopParse.Error (pos, msg) -> error no_loc "parse error at byte %d: %s" pos msg; exit 2
  | SLoopElab.Error msg -> error no_loc "elaboration error: %s" msg; exit 2
  | FrontendFailure msg -> error no_loc "%s" msg; exit 2
  | PlutoTilingValidator.ValidationError msg -> error no_loc "%s" msg; exit 2
  | CertcheckerConfig.CertCheckerFailure (_, msg) ->
      error no_loc "optimization failed inside extracted runtime: %s" msg; exit 2
  | e -> crash e
