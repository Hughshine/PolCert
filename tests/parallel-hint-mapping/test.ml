let fail case expected actual =
  Printf.eprintf
    "[parallel-hint-mapping] FAIL case=%s expected=%s actual=%s\n%!"
    case expected actual;
  exit 1

let pass case details =
  Printf.printf "[parallel-hint-mapping] PASS case=%s %s\n%!" case details

let read_file path =
  let channel = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let write_file path contents =
  let channel = open_out_bin path in
  Fun.protect
    ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel contents)

let replace_once ~case ~needle ~replacement text =
  let replaced =
    Str.replace_first (Str.regexp_string needle) replacement text
  in
  if String.equal replaced text then
    fail case "fixture marker present" "fixture marker absent";
  replaced

let loop_extension =
  "<loop>\n\
   1\n\
   t3\n\
   2\n\
   1\n\
   2\n\
   none\n\
   1\n\
   </loop>\n\n"

let with_t3_parallel_hint ~case text =
  replace_once
    ~case
    ~needle:"</OpenScop>"
    ~replacement:(loop_extension ^ "</OpenScop>")
    text

let parse_scop case path =
  match OpenScopReader.read path with
  | Some scop -> scop
  | None -> fail case "parseable OpenScop" "reader returned None"

let mapped_hints case path =
  let scop = parse_scop case path in
  let raw = Scheduler.extract_parallel_hints_from_outscop path in
  match Scheduler.map_parallel_hints_to_canonical_dims scop raw with
  | [hint] -> hint
  | hints ->
      fail case "one mapped hint" (Printf.sprintf "%d mapped hints" (List.length hints))

let assert_hint case hint ~raw ~canonical =
  let actual_raw = hint.Scheduler.hint_raw_dim in
  let actual_canonical = hint.Scheduler.hint_current_dim in
  if actual_raw <> raw || actual_canonical <> canonical then
    fail
      case
      (Printf.sprintf "raw=%d canonical=%d" raw canonical)
      (Printf.sprintf "raw=%d canonical=%d" actual_raw actual_canonical);
  if hint.Scheduler.hint_iterator <> "t3"
     || hint.Scheduler.hint_stmt_ids <> [1; 2]
  then
    fail case "iterator=t3 statements=[1,2]" "hint metadata changed";
  pass
    case
    (Printf.sprintf "raw=%d canonical=%d" actual_raw actual_canonical)

let with_temp_scop contents f =
  let path = Filename.temp_file "polcert-parallel-hint-" ".scop" in
  Fun.protect
    ~finally:(fun () -> if Sys.file_exists path then Sys.remove path)
    (fun () ->
       write_file path contents;
       f path)

let test_nonzero_scalar_row fixture =
  let text = read_file fixture |> with_t3_parallel_hint ~case:"nonzero-scalar-row" in
  with_temp_scop text (fun path ->
    let hint = mapped_hints "nonzero-scalar-row" path in
    assert_hint "nonzero-scalar-row" hint ~raw:2 ~canonical:2)

let test_globally_zero_row fixture =
  let nonzero_row =
    "   0    0   -1    0    0    0    0    1    ## c2 == 1"
  in
  let zero_row =
    "   0    0   -1    0    0    0    0    0    ## c2 == 0"
  in
  let text =
    read_file fixture
    |> replace_once
         ~case:"globally-zero-row"
         ~needle:nonzero_row
         ~replacement:zero_row
    |> with_t3_parallel_hint ~case:"globally-zero-row"
  in
  with_temp_scop text (fun path ->
    let hint = mapped_hints "globally-zero-row" path in
    assert_hint "globally-zero-row" hint ~raw:2 ~canonical:1)

let test_pluto_c_independence fixture =
  let text = read_file fixture |> with_t3_parallel_hint ~case:"pluto-c-independent" in
  with_temp_scop text (fun path ->
    let before = mapped_hints "pluto-c-independent" path in
    let sidecar = path ^ ".pluto.c" in
    Fun.protect
      ~finally:(fun () -> if Sys.file_exists sidecar then Sys.remove sidecar)
      (fun () ->
         write_file sidecar "for (t3 = 0; t3 < 1; ++t3) S1();\n";
         let compact = mapped_hints "pluto-c-independent" path in
         write_file sidecar "arbitrary formatting that is not C\n";
         let malformed = mapped_hints "pluto-c-independent" path in
         if before.Scheduler.hint_current_dim
              <> compact.Scheduler.hint_current_dim
            || before.Scheduler.hint_current_dim
              <> malformed.Scheduler.hint_current_dim
         then
           fail "pluto-c-independent" "unchanged canonical dimension"
             "sidecar changed mapping";
         pass "pluto-c-independent" "missing/reformatted sidecar ignored"))

let () =
  let fixture =
    "tools/tiling_routes/fixtures/fusion5-scalar-interleaved.midtransform.scop"
  in
  test_nonzero_scalar_row fixture;
  test_globally_zero_row fixture;
  test_pluto_c_independence fixture
