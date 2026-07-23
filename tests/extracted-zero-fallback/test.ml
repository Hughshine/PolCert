let fail label detail =
  Printf.eprintf "[extracted-zero-fallback] FAIL %s: %s\n" label detail;
  exit 1

let expect_certchecker_failure label thunk =
  try
    ignore (thunk ());
    fail label "returned instead of raising CertCheckerFailure"
  with
  | CertcheckerConfig.CertCheckerFailure _ -> ()
  | exn -> fail label ("raised unexpected exception: " ^ Printexc.to_string exn)

let expect_rejected_route label thunk =
  TilingValidationRoute.clear ();
  expect_certchecker_failure label thunk;
  match TilingValidationRoute.take () with
  | ["rejected"] -> ()
  | routes ->
      fail label
        ("expected route [rejected], observed ["
         ^ String.concat "; " routes ^ "]")

let expect_no_return label thunk =
  TilingValidationRoute.clear ();
  expect_certchecker_failure label thunk;
  ignore (TilingValidationRoute.take ())

let () =
  expect_rejected_route "SBandTilingOpt.reject_tiling"
    (fun () -> SBandTilingOpt.reject_tiling ());
  expect_no_return "SBandTilingOpt.Rejected selector"
    (fun () ->
      SBandTilingOpt.prepared_codegen_after_tiling_route
        SBandTilingOpt.PolyLang.dummy
        SBandTilingOpt.TilingSched.Rejected);
  expect_no_return "SBandTilingOpt post-tiling affine rejection"
    (fun () ->
      SBandTilingOpt.reject_post_tiling_affine
        SBandTilingOpt.TilingSched.DirectBandAccepted
        ());
  expect_rejected_route "SParallelPolOpt.reject_tiling"
    (fun () -> SParallelPolOpt.reject_tiling ());
  expect_no_return "SParallelPolOpt.Rejected selector"
    (fun () ->
      SParallelPolOpt.select_after_tiling_route
        SParallelPolOpt.PolyLang.dummy
        SParallelPolOpt.TilingSched.Rejected);
  expect_no_return "SParallelPolOpt post-tiling affine rejection"
    (fun () ->
      SParallelPolOpt.reject_post_tiling_affine
        SParallelPolOpt.TilingSched.DirectBandAccepted);
  Printf.printf
    "[extracted-zero-fallback] OK (6 direct extracted API rejection paths)\n"
