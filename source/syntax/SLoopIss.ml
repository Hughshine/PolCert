open Result
open SLoopCommon

let resolve_repo_file rel =
  let candidates =
    [ rel;
      Filename.concat (Sys.getcwd ()) rel;
      Filename.concat "/polcert" rel ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> frontend_failf "cannot locate repository file %s" rel

let run_python_tool args =
  let cmd =
    String.concat " "
      ("python3" :: List.map Filename.quote args)
  in
  Sys.command cmd

let read_all ic =
  let buf = Buffer.create 4096 in
  (try
     while true do
       Buffer.add_string buf (input_line ic);
       Buffer.add_char buf '\n'
     done
   with End_of_file -> ());
  Buffer.contents buf

let run_python_tool_capture args =
  let cmd =
    String.concat " "
      ("python3" :: List.map Filename.quote args)
  in
  let ic = Unix.open_process_in cmd in
  let output = read_all ic in
  let code =
    match Unix.close_process_in ic with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED n -> 128 + n
    | Unix.WSTOPPED n -> 128 + n
  in
  (code, output)

let split_on_char ch s =
  let rec go i j acc =
    if j = String.length s then
      List.rev (String.sub s i (j - i) :: acc)
    else if s.[j] = ch then
      go (j + 1) (j + 1) (String.sub s i (j - i) :: acc)
    else
      go i (j + 1) acc
  in
  go 0 0 []

let int_of_string_or_fail ctx s =
  try int_of_string s
  with Failure _ -> frontend_failf "cannot parse integer in %s: %S" ctx s

let z_of_string s =
  Camlcoq.Z.of_sint (int_of_string_or_fail "ISS bridge" s)

let parse_row_line line =
  match String.split_on_char ' ' line with
  | ["ROW"; payload] ->
      begin match split_on_char '|' payload with
      | [coeffs_s; const_s] ->
          let coeffs =
            if coeffs_s = "" then []
            else List.map z_of_string (split_on_char ',' coeffs_s)
          in
          (coeffs, z_of_string const_s)
      | _ ->
          frontend_failf "bad ISS bridge ROW payload: %S" payload
      end
  | _ ->
      frontend_failf "bad ISS bridge ROW line: %S" line

let iss_sign_of_string = function
  | "ge" -> ISSWitness.ISSCutGeZero
  | "lt" -> ISSWitness.ISSCutLtZero
  | s -> frontend_failf "unknown ISS halfspace sign %S in bridge JSON" s

type parsed_iss_bridge = {
  pib_var_order : string list;
  pib_before_domains : (Camlcoq.Z.t list * Camlcoq.Z.t) list list;
  pib_after_domains : (Camlcoq.Z.t list * Camlcoq.Z.t) list list;
  pib_witness : ISSWitness.iss_witness;
}

let build_iss_debug_pprog var_order stmt_domains =
  let module PL = SPolIRs.SPolIRs.PolyLang in
  let ctxt = List.map Camlcoq.intern_string var_order in
  let mk_pi domain =
    {
      PL.pi_depth = Datatypes.O;
      pi_instr = SPolIRs.SPolIRs.Instr.dummy_instr;
      pi_poly = domain;
      pi_schedule = [];
      pi_point_witness = PointWitness.PSWIdentity Datatypes.O;
      pi_transformation = [];
      pi_access_transformation = [];
      pi_waccess = [];
      pi_raccess = [];
    }
  in
  ((List.map mk_pi stmt_domains, ctxt), [])

let iss_bridge_text_present text =
  String.split_on_char '\n' text
  |> List.exists
       (fun line ->
         let line = String.trim line in
         String.length line >= 9 && String.sub line 0 9 = "VAR_ORDER")

let parse_iss_bridge_text text =
  let lines0 =
    String.split_on_char '\n' text
    |> List.filter (fun s -> String.trim s <> "")
  in
  let rec drop_preamble = function
    | [] -> frontend_failf "missing ISS bridge VAR_ORDER"
    | line :: rest as lines ->
        if String.length line >= 9 && String.sub line 0 9 = "VAR_ORDER"
        then lines
        else drop_preamble rest
  in
  let lines = drop_preamble lines0 in
  let rec take_rows n acc = function
    | [] -> frontend_failf "unexpected end of ISS bridge while reading %d rows" n
    | line :: rest ->
        if n = 0 then (List.rev acc, line :: rest)
        else take_rows (n - 1) (parse_row_line line :: acc) rest
  in
  let rec take_vars n acc = function
    | [] -> frontend_failf "unexpected end of ISS bridge while reading %d vars" n
    | line :: rest ->
        if n = 0 then (List.rev acc, line :: rest)
        else
          begin match String.split_on_char ' ' line with
          | ["VAR"; name] -> take_vars (n - 1) (name :: acc) rest
          | _ -> frontend_failf "bad ISS bridge VAR line: %S" line
          end
  in
  let rec take_domains tag n acc lines =
    if n = 0 then (List.rev acc, lines) else
    match lines with
    | [] -> frontend_failf "unexpected end of ISS bridge while reading %s domains" tag
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | [hdr; row_count_s] when hdr = tag ->
            let row_count = int_of_string_or_fail "ISS bridge domain row count" row_count_s in
            let (rows, rest') = take_rows row_count [] rest in
            take_domains tag (n - 1) (rows :: acc) rest'
        | _ ->
            frontend_failf "bad ISS bridge %s line: %S" tag line
        end
  in
  let rec take_cuts n acc lines =
    if n = 0 then (List.rev acc, lines) else
    match lines with
    | [] -> frontend_failf "unexpected end of ISS bridge while reading cuts"
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["CUT"; payload] ->
            let row = parse_row_line ("ROW " ^ payload) in
            take_cuts (n - 1) (row :: acc) rest
        | _ -> frontend_failf "bad ISS bridge CUT line: %S" line
        end
  in
  let rec take_stmt_witnesses n acc lines =
    if n = 0 then (List.rev acc, lines) else
    match lines with
    | [] -> frontend_failf "unexpected end of ISS bridge while reading stmt witnesses"
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["STMT_WITNESS"; parent_s; signs_s] ->
            let signs =
              if signs_s = "" then []
              else List.map iss_sign_of_string (split_on_char ',' signs_s)
            in
            let w =
              {
                ISSWitness.isw_parent_stmt = nat_of_int (int_of_string_or_fail "ISS bridge parent" parent_s);
                isw_piece_signs = signs;
              }
            in
            take_stmt_witnesses (n - 1) (w :: acc) rest
        | _ -> frontend_failf "bad ISS bridge STMT_WITNESS line: %S" line
        end
  in
  let var_order, rest1 =
    match lines with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["VAR_ORDER"; n_s] ->
            take_vars (int_of_string_or_fail "ISS bridge var count" n_s) [] rest
        | _ -> frontend_failf "bad ISS bridge header: %S" line
        end
    | [] -> frontend_failf "empty ISS bridge output"
  in
  let before_domains, rest2 =
    match rest1 with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["BEFORE_STMTS"; n_s] ->
            take_domains "BEFORE_DOMAIN" (int_of_string_or_fail "ISS bridge before stmt count" n_s) [] rest
        | _ -> frontend_failf "bad ISS bridge BEFORE_STMTS line: %S" line
        end
    | [] -> frontend_failf "missing ISS bridge BEFORE_STMTS"
  in
  let after_domains, rest3 =
    match rest2 with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["AFTER_STMTS"; n_s] ->
            take_domains "AFTER_DOMAIN" (int_of_string_or_fail "ISS bridge after stmt count" n_s) [] rest
        | _ -> frontend_failf "bad ISS bridge AFTER_STMTS line: %S" line
        end
    | [] -> frontend_failf "missing ISS bridge AFTER_STMTS"
  in
  let cuts, rest4 =
    match rest3 with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["CUTS"; n_s] ->
            take_cuts (int_of_string_or_fail "ISS bridge cut count" n_s) [] rest
        | _ -> frontend_failf "bad ISS bridge CUTS line: %S" line
        end
    | [] -> frontend_failf "missing ISS bridge CUTS"
  in
  let stmt_witnesses, rest5 =
    match rest4 with
    | line :: rest ->
        begin match String.split_on_char ' ' line with
        | ["STMT_WITNESSES"; n_s] ->
            take_stmt_witnesses (int_of_string_or_fail "ISS bridge stmt witness count" n_s) [] rest
        | _ -> frontend_failf "bad ISS bridge STMT_WITNESSES line: %S" line
        end
    | [] -> frontend_failf "missing ISS bridge STMT_WITNESSES"
  in
  begin match rest5 with
  | ["END"] -> ()
  | line :: _ -> frontend_failf "unexpected trailing ISS bridge line: %S" line
  | [] -> frontend_failf "missing ISS bridge END"
  end;
  let witness =
    {
      ISSWitness.iw_cuts = cuts;
      iw_stmt_witnesses = stmt_witnesses;
    }
  in
  {
    pib_var_order = var_order;
    pib_before_domains = before_domains;
    pib_after_domains = after_domains;
    pib_witness = witness;
  }

let parse_iss_bridge_text_opt text =
  if iss_bridge_text_present text then
    Some (parse_iss_bridge_text text)
  else
    None

let parsed_iss_bridge_to_dummy_pprogs bridge =
  ( build_iss_debug_pprog bridge.pib_var_order bridge.pib_before_domains,
    build_iss_debug_pprog bridge.pib_var_order bridge.pib_after_domains,
    bridge.pib_witness )

let read_text_file path =
  let ic = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () -> read_all ic)

let run_iss_bridge_validator bridge_file =
  let bridge = parse_iss_bridge_text (read_text_file bridge_file) in
  let (before_pol, after_pol, witness) =
    parsed_iss_bridge_to_dummy_pprogs bridge
  in
  let module ISS = ISSValidator.ISSValidator (SPolIRs.SPolIRs) in
  let ok =
    ISS.checked_iss_complete_cut_shape_validate before_pol after_pol witness
  in
  if ok then begin
    print_endline "validation: OK (coq complete-cut-shape)";
    0
  end else begin
    print_endline "validation: FAIL: extracted ISS complete-cut-shape checker rejected bridge witness";
    1
  end

let run_iss_dump_validator before_file after_file =
  let tool = resolve_repo_file "tools/iss/pluto_iss_check.py" in
  let (code, output) =
    run_python_tool_capture [tool; "--emit-bridge"; before_file; after_file]
  in
  if code <> 0 then begin
    print_string output;
    code
  end else
    let tmp = Filename.temp_file "iss-bridge-" ".txt" in
    let oc = open_out tmp in
    output_string oc output;
    close_out oc;
    Fun.protect
      ~finally:(fun () -> Sys.remove tmp)
      (fun () -> run_iss_bridge_validator tmp)

let run_iss_pluto_suite () =
  let tool = resolve_repo_file "tools/iss/run_pluto_iss_suite.py" in
  run_python_tool [tool]

let run_iss_pluto_live_suite () =
  let tool = resolve_repo_file "tools/iss/run_pluto_iss_live_suite.py" in
  run_python_tool [tool]
