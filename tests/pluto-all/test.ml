open Unix
open TPolIRs
open TPolValidator
open PolPrinter

let tests = [| 
    (** below is examples/ in pluto, that is compilable by candl frontend. *)
    "covcol"; "dsyr2k"; "fdtd-2d"; "gemver"; "lu"; "mvt"; "ssymm"; "tce";                 
    "adi"; "corcol"; "dct"; "dsyrk"; "floyd"; 
    "jacobi-1d-imper";
    "matmul-init"; "pca"; "strmm"; "tmm";                 
    "advect3d"; "corcol3"; "doitgen"; "fdtd-1d"; 
     "jacobi-2d-imper"; 
    "matmul"; "seidel"; "strsm"; "trisolv";
    (** below are in pluto's tests/  (they are truly tested in test.sh.in), and is compilable by candl frontend *)
    (** some of tests are also examples *)
    "1dloop-invar"; "costfunc"; 
    "fusion1"; "fusion2"; "fusion3"; "fusion4"; "fusion5";  
    "fusion6"; "fusion7"; "fusion8"; "fusion9"; "fusion10";  
    "intratileopt1"; "intratileopt2"; "intratileopt3"; "intratileopt4"; 
    "matmul-seq"; "matmul-seq3"; "multi-loop-param"; "multi-stmt-stencil-seq";
    "mxv"; "mxv-seq"; "mxv-seq3"; "negparam"; "nodep"; "noloop";
    "polynomial"; "seq"; "shift"; "spatial"; 
    "tricky1"; "tricky2"; "tricky3"; "tricky4"; "wavefront"
    |]

(* let tests = [| "3d7pt"; "apop"; "covcol"; "dsyr2k"; "fdtd-2d"; "gemver"; "heat-3d"; "lbm_fpc_d2q9"; "lbm_ldc_d3q27"; "lu"; "mvt"; "ssymm"; "tce";
                    "adi"; "corcol"; "dct"; "dsyrk"; "floyd"; "heat-1d"; "jacobi-1d-imper"; "lbm_ldc_d2q9"; "lbm_mrt_d2q9"; "matmul-init"; "pca"; "strmm"; "tmm";
                    "advect3d"; "corcol3"; "doitgen"; "fdtd-1d"; "game-of-life"; "heat-2d"; "jacobi-2d-imper"; "lbm_ldc_d3q19"; "lbm_poiseuille_d2q9"; "matmul"; "seidel"; "strsm"; "trisolv" |] *)


let example_tests = [| "noloop" |]

let folder_exists folder_path =
  Sys.file_exists folder_path && Sys.is_directory folder_path

(* let print_colored_text color_code text =
  Printf.printf "\027[%sm%s\027[0m" color_code text

let print_warning_message message =
  print_colored_text "33" message 33 is the ANSI code for yellow *)

let eval_result = ref []
let failed = ref false
let passed = ref 0

let report_failure test_name check expected actual interpretation =
  failed := true;
  Printf.eprintf
    "[legacy/pluto-all] FAIL case=%s check=%s expected=%s actual=%s interpretation=%s\n%!"
    test_name check expected actual interpretation

let test_single idx test_name =
  if not (folder_exists test_name) then begin
    report_failure test_name "fixture" "directory-present" "directory-missing"
      "the-Pluto-corpus-case-could-not-run"
  end else begin
  Printf.printf "\027[90mInfo\027[0m: Testing [[[ %d: %s ]]]... \n" (idx+1) test_name;
  let original_dir = Unix.getcwd () in
  Fun.protect ~finally:(fun () -> Unix.chdir original_dir) (fun () ->
  try
    Unix.chdir test_name;
    (* Printf.printf "Info: chdir to: %s\n" test_name; *)
    (match Scheduler.invoke_pluto test_name with
    | Okk (inscop, outscop, runtime) ->
        (* Printf.printf "Info: pluto success.\n"; *)
        (
        match TPolIRs.PolyLang.from_openscop_complete inscop, TPolIRs.PolyLang.from_openscop_complete outscop with
        | Okk inpol, Okk outpol -> 
            (
              (match TPolIRs.PolyLang.to_openscop inpol with
              | Some inscop -> OpenScopPrinter.openscop_printer "in.scop" inscop
              | None -> report_failure test_name "input-OpenScop-roundtrip"
                  "conversion-success" "conversion-failure"
                  "validated-input-could-not-be-re-encoded")
              ; 
              (match TPolIRs.PolyLang.to_openscop outpol with
              | Some inscop -> OpenScopPrinter.openscop_printer "out.scop" inscop
              | None -> report_failure test_name "output-OpenScop-roundtrip"
                  "conversion-success" "conversion-failure"
                  "optimized-output-could-not-be-re-encoded")
              ; 
            );
            (Printf.printf "\027[90mInfo\027[0m: poly transformation success\n";
            let t0 = Sys.time() in
            let (res1, ok1) = validate inpol outpol in
            let tv1 = Sys.time() -. t0 in
            let t0 = Sys.time() in
            let (res2, ok2) = validate outpol inpol in
            let tv2 = Sys.time() -. t0 in
            (if ok1 && res1 then
              ()
            else
              report_failure test_name "orig-to-opt" "ok:true,res:true"
                (Printf.sprintf "ok:%B,res:%B" ok1 res1)
                "forward-refinement-was-not-established"
            );
            (if ok2 && res2 then
                ()
              else
                report_failure test_name "opt-to-orig" "ok:true,res:true"
                  (Printf.sprintf "ok:%B,res:%B" ok2 res2)
                  "reverse-refinement-was-not-established");
            let valid1 = ok1 && res1 in
            let valid2 = ok2 && res2 in
            let result = (if valid1 && valid2 then "EQ" else if valid1 then "GT" else if valid2 then "LT" else "NEQ") in
            if valid1 && valid2 then begin
              passed := !passed + 1;
              Printf.printf
                "[legacy/pluto-all] PASS case=%s expected=forward:true,reverse:true actual=forward:%B,reverse:%B interpretation=schedules-are-mutually-refining\n%!"
                test_name valid1 valid2
            end;
            eval_result := List.append !eval_result [(test_name, Float.mul 1000.0 runtime, Float.mul 1000.0 tv1, Float.mul 1000.0 tv2, result)]);  (* ms *)
            Printf.printf "<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n%!"
        | _, _ -> 
            report_failure test_name "OpenScop-to-Poly"
              "input-and-output-convert" "conversion-failure"
              "the-scheduled-pair-could-not-be-validated"
        )
    | Err (err) ->
        report_failure test_name "scheduler" "success" "rejection"
          "Pluto-did-not-produce-a-schedule")
  with Unix_error (err, func, arg) ->
    report_failure test_name func "system-call-success"
      (Unix.error_message err) "the-case-could-not-complete");
  end

let print_result filename =
  let oc = open_out filename in
  Printf.fprintf oc "Test ToP ToB ToF Result\n";
  let lst = !eval_result in  (* Dereference the ref to access the list *)
  List.iter (fun (str, f1, f2, f3, str2) ->
    Printf.fprintf oc "%s %.2f %.2f %.2f %s\n" str f1 f2 f3 str2
  ) lst;
  close_out oc
;;

(* Main function *)
let () =
  (* Loop through each folder name in the array and test it *)
  Array.iteri test_single tests;
  print_result "../../result.txt";
  if !failed then begin
    Printf.eprintf
      "[legacy/pluto-all] FAIL expected=%d actual=%d interpretation=one-or-more-corpus-cases-failed\n%!"
      (Array.length tests) !passed;
    exit 1
  end else
    Printf.printf
      "[legacy/pluto-all] PASS expected=%d actual=%d interpretation=all-corpus-schedules-are-mutually-refining\n%!"
      (Array.length tests) !passed
  (* Array.iter test_single tests *)
