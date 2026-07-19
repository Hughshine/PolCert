

(* let scheduler  *)
open Result
open Driveraux
(* open CPolIRs *)
open Camlcoq
open Filename
open Str  (* Required for regular expressions *)

type pluto_parallel_hint = {
  hint_iterator : string;
  hint_current_dim : int;
  hint_directive : int;
}

type tiling_mode =
  | OrdinaryTiling
  | SecondLevelTiling

type diamond_mode =
  | NoDiamondTiling
  | DiamondTiling
  | FullDiamondTiling

let current_tiling_mode = ref OrdinaryTiling
let current_diamond_mode = ref NoDiamondTiling
let current_pluto_extra_flags = ref []
let current_pluto_control_files = ref []

let set_tiling_mode mode =
  current_tiling_mode := mode

let set_diamond_mode mode =
  current_diamond_mode := mode

let set_pluto_extra_flags flags =
  current_pluto_extra_flags := flags

let absolute_path path =
  if Filename.is_relative path then
    Filename.concat (Sys.getcwd ()) path
  else
    path

let set_pluto_control_files files =
  current_pluto_control_files :=
    List.map (fun (target, source) -> (target, absolute_path source)) files

let with_pluto_extra_flags flags =
  flags @ !current_pluto_extra_flags

let second_level_tiling_enabled () =
  !current_tiling_mode = SecondLevelTiling

let diamond_tiling_enabled () =
  !current_diamond_mode <> NoDiamondTiling

let full_diamond_tiling_enabled () =
  !current_diamond_mode = FullDiamondTiling

let tmp_file_abs suff =
  absolute_path (tmp_file suff)

let copy_file src dst =
  let ic = open_in_bin src in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () ->
      let oc = open_out_bin dst in
      Fun.protect
        ~finally:(fun () -> close_out_noerr oc)
        (fun () ->
          let buf = Bytes.create 65536 in
          let rec loop () =
            let n = input ic buf 0 (Bytes.length buf) in
            if n > 0 then begin
              output oc buf 0 n;
              loop ()
            end
          in
          loop ()))

let with_pluto_control_workdir f =
  match !current_pluto_control_files with
  | [] -> f ()
  | files ->
      let installed = ref [] in
      Fun.protect
        ~finally:(fun () ->
          List.iter safe_remove !installed)
        (fun () ->
          List.iter
            (fun (target, source) ->
              if Sys.file_exists target then
                failwith
                  (Printf.sprintf
                     "explicit Pluto control file target %s already exists in the oracle working directory"
                     target);
              installed := target :: !installed;
              copy_file source target)
            files;
          f ())

let pluto_executable () =
  match Sys.getenv_opt "POLCERT_PLUTO" with
  | Some path when String.trim path <> "" -> path
  | _ ->
      let container_pluto = "/pluto/tool/pluto" in
      if Sys.file_exists container_pluto then
        container_pluto
      else
        "pluto"

let resolve_repo_file rel =
  let candidates =
    [ rel;
      Filename.concat (Sys.getcwd ()) rel;
      Filename.concat "/polcert" rel ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> failwith ("cannot locate repository file " ^ rel)

let read_file path =
  let ic = open_in path in
  let buf = Buffer.create 4096 in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () ->
      (try
         while true do
           Buffer.add_string buf (input_line ic);
           Buffer.add_char buf '\n'
         done
       with End_of_file -> ());
      Buffer.contents buf)

let implicit_pluto_control_files = []

let implicit_pluto_control_file_error () =
  match List.find_opt Sys.file_exists implicit_pluto_control_files with
  | None -> None
  | Some path ->
      Some
        (coqstring_of_camlstring
           (Printf.sprintf
              "implicit Pluto control file %s is not supported by polopt; remove it or use a future explicit file option"
              path))

(** scop to scop *)

(** TODO: specify dump scop file name in pluto*)
let run_pluto_scop flags inscop =
  match implicit_pluto_control_file_error () with
  | Some msg -> Err msg
  | None ->
  let inscop_file = tmp_file_abs ".scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [[pluto_executable (); "--dumpscop"; "--readscop"]; flags; [inscop_file]]
  in
  (* print_string ((String.concat " " cmd) ^ "\n"); *)
  let stdout = tmp_file_abs ".stdout" in
  let exc =
    with_pluto_control_workdir
      (fun () -> command ?stdout:(Some stdout) cmd)
  in
  let read_outscop () =
      if Sys.file_exists outscop_file then
      OpenScopReader.read outscop_file
    else
      None
  in
  match read_outscop () with
  | Some outscop -> Okk outscop
  | None ->
      if exc <> 0 then (
        safe_remove outscop_file;
        Err
          (coqstring_of_camlstring
             (Printf.sprintf "scheduler failed with exit code %d" exc))
      ) else
        Err (coqstring_of_camlstring ("scheduler failed"))

let text_has_line tag text =
  String.split_on_char '\n' text
  |> List.exists (fun line -> String.trim line = tag)

let run_pluto_scop_with_midpoint_and_posttile_dump flags inscop =
  match implicit_pluto_control_file_error () with
  | Some msg -> Err msg
  | None ->
  let inscop_file = tmp_file_abs ".scop" in
  let midscop_file = inscop_file ^ ".midtransform.scop" in
  let posttile_file = inscop_file ^ ".posttile.scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [[pluto_executable (); "--dumpscop"; "--readscop"]; flags; [inscop_file]]
  in
  let stdout = tmp_file_abs ".stdout" in
  let exc =
    with_pluto_control_workdir
      (fun () -> command ?stdout:(Some stdout) cmd)
  in
  let read_scop path =
    if Sys.file_exists path then
      OpenScopReader.read path
    else
      None
  in
  match read_scop midscop_file, read_scop posttile_file, read_scop outscop_file with
  | Some midscop, Some posttile_scop, Some outscop -> Okk (midscop, posttile_scop, outscop)
  | _ ->
      if exc <> 0 then (
        safe_remove midscop_file;
        safe_remove posttile_file;
        safe_remove outscop_file;
        Err
          (coqstring_of_camlstring
             (Printf.sprintf "diamond scheduler failed with exit code %d" exc))
      ) else
        Err (coqstring_of_camlstring "diamond scheduler failed")

let trim_nonempty_lines lines =
  List.filter_map
    (fun line ->
      let line = String.trim line in
      if line = "" then None else Some line)
    lines

let payload_lines_between_tags begin_tag end_tag text =
  let rec seek = function
    | [] -> []
    | line :: rest ->
        if String.trim line = begin_tag then
          collect [] rest
        else
          seek rest
  and collect acc = function
    | [] -> List.rev acc
    | line :: rest ->
        if String.trim line = end_tag then
          List.rev acc
        else
          collect (line :: acc) rest
  in
  seek (String.split_on_char '\n' text)

let noncomment_payload_lines lines =
  trim_nonempty_lines lines
  |> List.filter (fun line -> line.[0] <> '#')

let split_ws s =
  List.filter (fun tok -> tok <> "")
    (Str.split (Str.regexp "[ \t\r]+") s)

let concat_map f xs =
  List.concat (List.map f xs)

let take n xs =
  let rec go k acc ys =
    if k <= 0 then List.rev acc
    else match ys with
      | [] -> List.rev acc
      | y :: ys' -> go (k - 1) (y :: acc) ys'
  in
  go n [] xs

let drop n xs =
  let rec go k ys =
    if k <= 0 then ys
    else match ys with
      | [] -> []
      | _ :: ys' -> go (k - 1) ys'
  in
  go n xs

let extract_loop_hints_from_outscop directive_mask outscop_file =
  try
    let text = read_file outscop_file in
    let scatnames =
      payload_lines_between_tags "<scatnames>" "</scatnames>" text
      |> noncomment_payload_lines
      |> concat_map split_ws
    in
    let loop_payload =
      payload_lines_between_tags "<loop>" "</loop>" text
      |> noncomment_payload_lines
    in
    let parse_loop_entries payload =
      match payload with
      | [] -> []
      | loop_count_s :: rest ->
          let loop_count = int_of_string loop_count_s in
          let rec parse count acc lines =
            if count <= 0 then List.rev acc
            else
              match lines with
              | iterator :: stmt_nb_s :: tail ->
                  let stmt_nb = int_of_string stmt_nb_s in
                  let stmt_ids = take stmt_nb tail in
                  if List.length stmt_ids <> stmt_nb then
                    raise (Failure "loop stmt id count mismatch");
                  begin
                    match drop stmt_nb tail with
                    | _private_vars :: directive_s :: rest' ->
                        let directive = int_of_string directive_s in
                        parse (count - 1) ((iterator, directive) :: acc) rest'
                    | _ ->
                        raise (Failure "truncated loop extension")
                  end
              | _ ->
                  raise (Failure "truncated loop extension")
          in
          parse loop_count [] rest
    in
    let loop_entries = parse_loop_entries loop_payload in
    let rec find_index iterator i = function
      | [] -> None
      | name :: rest ->
          if String.equal name iterator then Some i
          else find_index iterator (i + 1) rest
    in
    let rec add_unique seen acc = function
      | [] -> List.rev acc
      | (iterator, directive) :: rest ->
          if directive land directive_mask = 0 then
            add_unique seen acc rest
          else
            match find_index iterator 0 scatnames with
            | None -> add_unique seen acc rest
            | Some dim ->
                if List.mem dim seen then
                  add_unique seen acc rest
                else
                  let hint =
                    {
                      hint_iterator = iterator;
                      hint_current_dim = dim;
                      hint_directive = directive;
                    }
                  in
                  add_unique (dim :: seen) (hint :: acc) rest
    in
    add_unique [] [] loop_entries
  with
  | Sys_error _
  | Failure _ -> []

let extract_parallel_hints_from_outscop outscop_file =
  extract_loop_hints_from_outscop 1 outscop_file

let extract_vector_hints_from_outscop outscop_file =
  extract_loop_hints_from_outscop 4 outscop_file

let extract_parallel_hint_from_outscop outscop_file =
  match extract_parallel_hints_from_outscop outscop_file with
  | [] -> None
  | hint :: _ -> Some hint

let extract_vector_hint_from_outscop outscop_file =
  match extract_vector_hints_from_outscop outscop_file with
  | [] -> None
  | hint :: _ -> Some hint

let run_pluto_scop_with_loop_hint extractor flags inscop =
  match implicit_pluto_control_file_error () with
  | Some msg -> Err msg
  | None ->
  let inscop_file = tmp_file_abs ".scop" in
  let outscop_file = inscop_file ^ ".afterscheduling.scop" in
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [[pluto_executable (); "--dumpscop"; "--readscop"]; flags; [inscop_file]]
  in
  let stdout = tmp_file_abs ".stdout" in
  let exc =
    with_pluto_control_workdir
      (fun () -> command ?stdout:(Some stdout) cmd)
  in
  let read_outscop () =
    if Sys.file_exists outscop_file then
      OpenScopReader.read outscop_file
    else
      None
  in
  let hints = extractor outscop_file in
  match read_outscop () with
  | Some outscop -> Okk (outscop, hints)
  | None ->
      if exc <> 0 then (
        safe_remove outscop_file;
        Err
          (coqstring_of_camlstring
             (Printf.sprintf "scheduler failed with exit code %d" exc))
      ) else
        Err (coqstring_of_camlstring ("scheduler failed"))

let run_pluto_scop_with_parallel_hint flags inscop =
  run_pluto_scop_with_loop_hint extract_parallel_hints_from_outscop flags inscop

let run_pluto_scop_with_vector_hint flags inscop =
  run_pluto_scop_with_loop_hint extract_vector_hints_from_outscop flags inscop

let run_pluto_bridge flags inscop =
  match implicit_pluto_control_file_error () with
  | Some msg -> Err msg
  | None ->
  let inscop_file = tmp_file_abs ".scop" in
  let stdout_file = tmp_file_abs ".stdout" in
  OpenScopPrinter.openscop_printer inscop_file inscop;
  let cmd =
    List.concat
      [[pluto_executable (); "--readscop"]; flags; [inscop_file]]
  in
  let exc =
    with_pluto_control_workdir
      (fun () -> command ?stdout:(Some stdout_file) cmd)
  in
  let output = read_file stdout_file in
  if exc <> 0 then
    Err
      (coqstring_of_camlstring
         (Printf.sprintf "ISS debug dump export failed with exit code %d" exc))
  else if not (text_has_line "After ISS" output) then
    Okk output
  else
    try
      let bridge_tool = resolve_repo_file "tools/iss/pluto_iss_check.py" in
      let bridge_stdout = tmp_file_abs ".bridge.stdout" in
      let bridge_cmd =
        [ "python3";
          bridge_tool;
          "--emit-bridge-from-combined";
          stdout_file ]
      in
      let bridge_exc = command ?stdout:(Some bridge_stdout) bridge_cmd in
      let bridge_output = read_file bridge_stdout in
      if bridge_exc = 0 then
        Okk bridge_output
      else
        Err
          (coqstring_of_camlstring
             (Printf.sprintf
                "ISS bridge recovery from Pluto debug dump failed with exit code %d"
                bridge_exc))
    with Failure msg ->
      Err (coqstring_of_camlstring msg)

let affine_only_flags =
  [
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar";
  ]

let tile_only_flags =
  [
    "--identity";
    "--tile";
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--nounrolljam";
    "--noparallel";
    "--rar";
  ]

let tile_only_second_level_flags =
  tile_only_flags @ ["--second-level-tile"]

let affine_with_iss_flags =
  ["--iss"] @ affine_only_flags

let affine_only_parallel_flags =
  [
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--parallel";
    "--notile";
    "--rar";
  ]

let affine_only_vector_flags =
  [
    "--nointratileopt";
    "--nodiamond-tile";
    "--prevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar";
  ]

let tile_only_parallel_flags =
  [
    "--identity";
    "--tile";
    (* Keep the tiled schedule canonical so the verified tiling witness
       stays phase-aligned. Pluto's default tiled --parallel path may
       skew tiles for wavefront parallelism. *)
    "--innerpar";
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--nounrolljam";
    "--parallel";
    "--rar";
  ]

let tile_only_vector_flags =
  [
    "--identity";
    "--tile";
    "--nointratileopt";
    "--nodiamond-tile";
    "--prevector";
    "--nounrolljam";
    "--noparallel";
    "--rar";
  ]

let tile_only_parallel_second_level_flags =
  tile_only_parallel_flags @ ["--second-level-tile"]

let tile_only_vector_second_level_flags =
  tile_only_vector_flags @ ["--second-level-tile"]

let second_level_tiling_flags () =
  if second_level_tiling_enabled ()
  then ["--second-level-tile"]
  else []

let diamond_phase_flags () =
  [
    "--tile";
    "--nointratileopt";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
    "--rar";
  ]
  @
  (if full_diamond_tiling_enabled ()
   then ["--diamond-tile"; "--full-diamond-tile"]
   else ["--diamond-tile"])
  @
  second_level_tiling_flags ()

let diamond_phase_parallel_flags () =
  [
    "--tile";
    "--nointratileopt";
    "--noprevector";
    "--smartfuse";
    "--nounrolljam";
    "--parallel";
    "--rar";
  ]
  @
  (if full_diamond_tiling_enabled ()
   then ["--diamond-tile"; "--full-diamond-tile"]
   else ["--diamond-tile"])
  @
  second_level_tiling_flags ()

let diamond_phase_parallel_with_iss_flags () =
  "--iss" :: diamond_phase_parallel_flags ()

let diamond_phase_vector_flags () =
  [
    "--tile";
    "--nointratileopt";
    "--prevector";
    "--smartfuse";
    "--nounrolljam";
    "--noparallel";
    "--rar";
  ]
  @
  (if full_diamond_tiling_enabled ()
   then ["--diamond-tile"; "--full-diamond-tile"]
   else ["--diamond-tile"])
  @
  second_level_tiling_flags ()

let diamond_phase_vector_with_iss_flags () =
  "--iss" :: diamond_phase_vector_flags ()

let diamond_phase_with_iss_flags () =
  "--iss" :: diamond_phase_flags ()

let affine_with_iss_parallel_flags =
  ["--iss"] @ affine_only_parallel_flags

let affine_with_iss_vector_flags =
  ["--iss"] @ affine_only_vector_flags

let iss_identity_bridge_flags =
  [
    "--iss";
    "--identity";
    "--moredebug";
    "--silent";
  ]

let affine_only_scop_scheduler inscop =
  run_pluto_scop (with_pluto_extra_flags affine_only_flags) inscop

let tile_only_scop_scheduler inscop =
  let flags =
    if second_level_tiling_enabled ()
    then tile_only_second_level_flags
    else tile_only_flags
  in
  run_pluto_scop (with_pluto_extra_flags flags) inscop

let affine_only_scop_scheduler_with_parallel_hint inscop =
  run_pluto_scop_with_parallel_hint
    (with_pluto_extra_flags affine_only_parallel_flags)
    inscop

let affine_only_scop_scheduler_with_vector_hint inscop =
  run_pluto_scop_with_vector_hint
    (with_pluto_extra_flags affine_only_vector_flags)
    inscop

let tile_only_scop_scheduler_with_parallel_hint inscop =
  let flags =
    if second_level_tiling_enabled ()
    then tile_only_parallel_second_level_flags
    else tile_only_parallel_flags
  in
  run_pluto_scop_with_parallel_hint (with_pluto_extra_flags flags) inscop

let tile_only_scop_scheduler_with_vector_hint inscop =
  let flags =
    if second_level_tiling_enabled ()
    then tile_only_vector_second_level_flags
    else tile_only_vector_flags
  in
  run_pluto_scop_with_vector_hint (with_pluto_extra_flags flags) inscop

let affine_only_scop_scheduler_with_iss inscop =
  run_pluto_scop (with_pluto_extra_flags affine_with_iss_flags) inscop

let affine_only_scop_scheduler_with_iss_with_parallel_hint inscop =
  run_pluto_scop_with_parallel_hint
    (with_pluto_extra_flags affine_with_iss_parallel_flags)
    inscop

let affine_only_scop_scheduler_with_iss_with_vector_hint inscop =
  run_pluto_scop_with_vector_hint
    (with_pluto_extra_flags affine_with_iss_vector_flags)
    inscop

let iss_identity_bridge_from_scop inscop =
  run_pluto_bridge iss_identity_bridge_flags inscop

let run_pluto_phase_pipeline inscop =
  match affine_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler midscop with
        | Err msg -> Err msg
        | Okk outscop ->
            if second_level_tiling_enabled () then
              begin
                try
                  let artifact =
                    PlutoTilingValidator.extract_phase_artifact_from_scops
                      ~tiling_mode:PlutoTilingValidator.SecondLevel
                      ~before_path:"mid_affine"
                      ~after_path:"after_tiled"
                      midscop
                      outscop
                  in
                  Okk (midscop, artifact.artifact_after_scop)
                with
                | PlutoTilingValidator.ValidationError msg ->
                    Err (coqstring_of_camlstring msg)
                | exn ->
                    Err (coqstring_of_camlstring (Printexc.to_string exn))
              end
            else
              Okk (midscop, outscop)
      end

let run_pluto_identity_tiling_pipeline inscop =
  match tile_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk outscop ->
      if second_level_tiling_enabled () then
        begin
          try
            let artifact =
              PlutoTilingValidator.extract_phase_artifact_from_scops
                ~tiling_mode:PlutoTilingValidator.SecondLevel
                ~before_path:"identity_before"
                ~after_path:"identity_tiled"
                inscop
                outscop
            in
            Okk (inscop, artifact.artifact_after_scop)
          with
          | PlutoTilingValidator.ValidationError msg ->
              Err (coqstring_of_camlstring msg)
          | exn ->
              Err (coqstring_of_camlstring (Printexc.to_string exn))
        end
      else
        Okk (inscop, outscop)

let run_pluto_diamond_phase_pipeline inscop =
  run_pluto_scop_with_midpoint_and_posttile_dump
    (with_pluto_extra_flags (diamond_phase_flags ()))
    inscop

let run_pluto_diamond_phase_pipeline_nested inscop =
  match run_pluto_diamond_phase_pipeline inscop with
  | Err msg -> Err msg
  | Okk (midscop, posttile_scop, after_scop) ->
      Okk (midscop, (posttile_scop, after_scop))

let run_pluto_diamond_phase_pipeline_with_iss inscop =
  run_pluto_scop_with_midpoint_and_posttile_dump
    (with_pluto_extra_flags (diamond_phase_with_iss_flags ()))
    inscop

let run_pluto_diamond_phase_pipeline_with_iss_nested inscop =
  match run_pluto_diamond_phase_pipeline_with_iss inscop with
  | Err msg -> Err msg
  | Okk (midscop, posttile_scop, after_scop) ->
      Okk (midscop, (posttile_scop, after_scop))

let run_pluto_phase_pipeline_with_parallel_hint inscop =
  match affine_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler_with_parallel_hint midscop with
        | Err msg -> Err msg
        | Okk (outscop, hint) -> Okk (midscop, outscop, hint)
      end

let run_pluto_phase_pipeline_with_vector_hint inscop =
  match affine_only_scop_scheduler inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler_with_vector_hint midscop with
        | Err msg -> Err msg
        | Okk (outscop, hint) -> Okk (midscop, outscop, hint)
      end

let run_pluto_diamond_parallel_hint inscop =
  match run_pluto_scop_with_parallel_hint
          (with_pluto_extra_flags (diamond_phase_parallel_flags ()))
          inscop with
  | Err msg -> Err msg
  | Okk (_outscop, hint) -> Okk hint

let run_pluto_diamond_parallel_hint_with_iss inscop =
  match run_pluto_scop_with_parallel_hint
          (with_pluto_extra_flags (diamond_phase_parallel_with_iss_flags ()))
          inscop with
  | Err msg -> Err msg
  | Okk (_outscop, hint) -> Okk hint

let run_pluto_diamond_vector_hint inscop =
  match run_pluto_scop_with_vector_hint
          (with_pluto_extra_flags (diamond_phase_vector_flags ()))
          inscop with
  | Err msg -> Err msg
  | Okk (_outscop, hint) -> Okk hint

let run_pluto_diamond_vector_hint_with_iss inscop =
  match run_pluto_scop_with_vector_hint
          (with_pluto_extra_flags (diamond_phase_vector_with_iss_flags ()))
          inscop with
  | Err msg -> Err msg
  | Okk (_outscop, hint) -> Okk hint

let run_pluto_phase_pipeline_with_iss inscop =
  match affine_only_scop_scheduler_with_iss inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler midscop with
        | Err msg -> Err msg
        | Okk outscop ->
            if second_level_tiling_enabled () then
              begin
                try
                  let artifact =
                    PlutoTilingValidator.extract_phase_artifact_from_scops
                      ~tiling_mode:PlutoTilingValidator.SecondLevel
                      ~before_path:"mid_affine"
                      ~after_path:"after_tiled"
                      midscop
                      outscop
                  in
                  Okk (midscop, artifact.artifact_after_scop)
                with
                | PlutoTilingValidator.ValidationError msg ->
                    Err (coqstring_of_camlstring msg)
                | exn ->
                    Err (coqstring_of_camlstring (Printexc.to_string exn))
              end
            else
              Okk (midscop, outscop)
      end

let run_pluto_phase_pipeline_with_iss_with_parallel_hint inscop =
  match affine_only_scop_scheduler_with_iss inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler_with_parallel_hint midscop with
        | Err msg -> Err msg
        | Okk (outscop, hint) -> Okk (midscop, outscop, hint)
      end

let run_pluto_phase_pipeline_with_iss_with_vector_hint inscop =
  match affine_only_scop_scheduler_with_iss inscop with
  | Err msg -> Err msg
  | Okk midscop ->
      begin
        match tile_only_scop_scheduler_with_vector_hint midscop with
        | Err msg -> Err msg
        | Okk (outscop, hint) -> Okk (midscop, outscop, hint)
      end

let phase_scop_scheduler = run_pluto_phase_pipeline

let infer_tiling_witness_scops before_scop after_scop =
  try
    let witness =
      let tiling_mode =
        if second_level_tiling_enabled ()
        then PlutoTilingValidator.SecondLevel
        else PlutoTilingValidator.Ordinary
      in
      PlutoTilingValidator.extract_witness_from_scops
        ~tiling_mode
        ~before_path:"mid_affine"
        ~after_path:"after_tiled"
        before_scop
        after_scop
    in
    Okk (PhaseTiling.convert_witness witness)
  with
  | PlutoTilingValidator.ValidationError msg ->
      Err (coqstring_of_camlstring msg)
  | exn ->
      Err (coqstring_of_camlstring (Printexc.to_string exn))

let scheduler' = affine_only_scop_scheduler


let find_and_extract_time filename =
  let ic = open_in filename in
  let rec process_lines () =
    try
      let line = input_line ic in
      let regex = regexp "\\[pluto\\] Auto-transformation time: \\([0-9.]+\\)s" in
      if string_match regex line 0 then begin
        let time_str = matched_group 1 line in
        let time_float = float_of_string time_str in
        close_in ic;
        time_float
      end else
        process_lines ()
    with
      End_of_file -> close_in ic; max_float
  in
  process_lines ()


(* also return the autoscheduling time, in pluto's stdout, "Auto-transformation time" *)
let invoke_pluto testname =
  let inscop_file = testname ^ ".beforescheduling.scop" in
  let outscop_file = testname ^ ".afterscheduling.scop" in
  let cmd = List.concat [
    [pluto_executable ();
    "--dumpscop";
    "--nointratileopt";
    "--nodiamond-tile";
    "--noprevector";
    "--smartfuse";     
    "--nounrolljam";
    "--noparallel";
    "--notile";
    "--rar"];
    [testname ^ ".c"]
  ] in
  let stdout =  (tmp_file ("." ^ testname ^ ".stdout")) in
  print_string ("\027[90mInfo\027[0m: Executing \"" ^ (String.concat " " cmd) ^ "\"\n");
  let exc = command ?stdout:(Some stdout) cmd in
  if exc <> 0 then (
    command_error "invoke pluto failed" exc;)
  else 
    (* [pluto] Auto-transformation time: 0.001530s *)
    let runtime = find_and_extract_time stdout in
    Printf.printf "\027[90mInfo\027[0m: Invoke pluto succeed, with auto-transformation time %fs\n" runtime;
    print_string ("\027[90mInfo\027[0m: Reading " ^ (inscop_file) ^ " ...\n");
    match OpenScopReader.read inscop_file with 
    | Some inscop -> 
      print_string ("\027[90mInfo\027[0m: Read " ^ (inscop_file) ^ " successfully\n");
      (match OpenScopReader.read outscop_file with 
      | Some outscop ->
        print_string ("\027[90mInfo\027[0m: Read " ^ (outscop_file) ^ " successfully\n");
        Okk (inscop, outscop, runtime)
      | None -> Err (coqstring_of_camlstring ("invoke pluto failed"))
      )
    | None -> Err (coqstring_of_camlstring ("invoke pluto failed")) 
    
  (* match OpenScopReader.read inscop_file with
  | Some outscop -> Okk outscop
  | None -> Err (coqstring_of_camlstring ("cannot read " ^ inscop_file ^ "\n")) *)

(* let scheduler' cpol =
  let inscop = CPolIRs.PolyLang.to_openscop cpol in
  let inscop_file = tmp_file ".scop" in
  let outscop_file = tmp_file ".scop" in 
  OpenScopPrinter.openscop_printer inscop_file inscop;
  match OpenScopReader.read inscop_file with
  | Some outscop -> CPolIRs.PolyLang.from_openscop cpol outscop
  | None -> Err (coqstring_of_camlstring ("Error: cannot read " ^ inscop_file ^ "\n")) *)

let scop_scheduler inscop = scheduler' inscop;;
