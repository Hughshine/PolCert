type stage_timing = string * float
type profile_metric = string * int

let time_stage timings name f =
  let started = Unix.gettimeofday () in
  let res = f () in
  let elapsed = Unix.gettimeofday () -. started in
  timings := !timings @ [name, elapsed];
  res

let print_stage_timings timings =
  let total = List.fold_left (fun acc (_, dt) -> acc +. dt) 0.0 timings in
  Printf.eprintf "[profile] stage timings\n";
  List.iter
    (fun (name, dt) ->
      Printf.eprintf "[profile]   %-24s %.6fs\n" name dt)
    timings;
  Printf.eprintf "[profile]   %-24s %.6fs\n" "total" total

let add_metric metrics name value =
  metrics := !metrics @ [name, value]

let print_profile_metrics metrics =
  if metrics <> [] then begin
    Printf.eprintf "[profile] structural metrics\n";
    List.iter
      (fun (name, value) ->
        Printf.eprintf "[profile]   %-24s %d\n" name value)
      metrics
  end

type polyloop_stats = {
  pl_nodes : int;
  pl_loops : int;
  pl_guards : int;
  pl_instrs : int;
  pl_seqs : int;
  pl_constraints : int;
}

let polyloop_stats_zero =
  {
    pl_nodes = 0;
    pl_loops = 0;
    pl_guards = 0;
    pl_instrs = 0;
    pl_seqs = 0;
    pl_constraints = 0;
  }

let add_polyloop_stats a b =
  {
    pl_nodes = a.pl_nodes + b.pl_nodes;
    pl_loops = a.pl_loops + b.pl_loops;
    pl_guards = a.pl_guards + b.pl_guards;
    pl_instrs = a.pl_instrs + b.pl_instrs;
    pl_seqs = a.pl_seqs + b.pl_seqs;
    pl_constraints = a.pl_constraints + b.pl_constraints;
  }

let rec polyloop_stats_of_stmt stmt =
  match stmt with
  | SPolOpt.CoreOpt.CodeGen.PolyLoop.PLoop (pol, inner) ->
      add_polyloop_stats
        { polyloop_stats_zero with pl_nodes = 1; pl_loops = 1; pl_constraints = List.length pol }
        (polyloop_stats_of_stmt inner)
  | SPolOpt.CoreOpt.CodeGen.PolyLoop.PInstr (_, _) ->
      { polyloop_stats_zero with pl_nodes = 1; pl_instrs = 1 }
  | SPolOpt.CoreOpt.CodeGen.PolyLoop.PSkip ->
      { polyloop_stats_zero with pl_nodes = 1 }
  | SPolOpt.CoreOpt.CodeGen.PolyLoop.PSeq (s1, s2) ->
      add_polyloop_stats
        { polyloop_stats_zero with pl_nodes = 1; pl_seqs = 1 }
        (add_polyloop_stats (polyloop_stats_of_stmt s1) (polyloop_stats_of_stmt s2))
  | SPolOpt.CoreOpt.CodeGen.PolyLoop.PGuard (pol, inner) ->
      add_polyloop_stats
        { polyloop_stats_zero with pl_nodes = 1; pl_guards = 1; pl_constraints = List.length pol }
        (polyloop_stats_of_stmt inner)

type loop_stats = {
  loop_nodes : int;
  loop_loops : int;
  loop_guards : int;
  loop_instrs : int;
  loop_seqs : int;
}

let loop_stats_zero =
  { loop_nodes = 0; loop_loops = 0; loop_guards = 0; loop_instrs = 0; loop_seqs = 0 }

let add_loop_stats a b =
  {
    loop_nodes = a.loop_nodes + b.loop_nodes;
    loop_loops = a.loop_loops + b.loop_loops;
    loop_guards = a.loop_guards + b.loop_guards;
    loop_instrs = a.loop_instrs + b.loop_instrs;
    loop_seqs = a.loop_seqs + b.loop_seqs;
  }

let rec loop_stmt_list_stats = function
  | SPolOpt.CoreOpt.CodeGen.LoopGen.Loop.SNil -> loop_stats_zero
  | SPolOpt.CoreOpt.CodeGen.LoopGen.Loop.SCons (stmt, rest) ->
      add_loop_stats (loop_stmt_stats stmt) (loop_stmt_list_stats rest)

and loop_stmt_stats stmt =
  match stmt with
  | SPolOpt.CoreOpt.CodeGen.LoopGen.Loop.Loop (_, _, inner) ->
      add_loop_stats
        { loop_stats_zero with loop_nodes = 1; loop_loops = 1 }
        (loop_stmt_stats inner)
  | SPolOpt.CoreOpt.CodeGen.LoopGen.Loop.Instr (_, _) ->
      { loop_stats_zero with loop_nodes = 1; loop_instrs = 1 }
  | SPolOpt.CoreOpt.CodeGen.LoopGen.Loop.Seq stmts ->
      add_loop_stats
        { loop_stats_zero with loop_nodes = 1; loop_seqs = 1 }
        (loop_stmt_list_stats stmts)
  | SPolOpt.CoreOpt.CodeGen.LoopGen.Loop.Guard (_, inner) ->
      add_loop_stats
        { loop_stats_zero with loop_nodes = 1; loop_guards = 1 }
        (loop_stmt_stats inner)
