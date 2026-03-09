open Diagnostics
open TPolOpt

let tool_name = "Verified Polyhedral Optimizer"

let touch_opt () =
  ignore opt

let _ =
  try
    Gc.set { (Gc.get()) with
                Gc.minor_heap_size = 524288; (* 512k *)
                Gc.major_heap_increment = 4194304 (* 4M *)
            };
    touch_opt ();
    if Array.length Sys.argv < 2 then
      Printf.printf "Usage: %s <loop-input-not-wired>\n" Sys.argv.(0)
    else
      Printf.printf "polopt frontend is not wired yet; TPolOpt.opt expects a Loop program.\n"
  with
  | Sys_error msg -> error no_loc "%s" msg; exit 2
  | e -> crash e
