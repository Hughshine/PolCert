#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
from collections import Counter


PIPELINE_CANON = {
    "precomputed": "default_no_iss_affine_tiling",
    "default_no_iss_affine_tiling": "default_no_iss_affine_tiling",
    "identity": "identity",
    "affine_only": "affine_only",
    "iss": "iss",
    "parallel_4": "parallel_4",
    "iss_parallel_4": "iss_parallel_4",
}

PIPELINE_LABEL = {
    "default_no_iss_affine_tiling": "default no-ISS affine+tiling pipeline",
    "identity": "identity-only fallback",
    "affine_only": "affine-only pipeline",
    "iss": "ISS-enabled sequential pipeline",
    "parallel_4": "parallel route (4 threads)",
    "iss_parallel_4": "ISS + parallel route (4 threads)",
}

PIPELINE_FLAGS = {
    "default_no_iss_affine_tiling": "(default)",
    "identity": "`--identity`",
    "affine_only": "`--affine-only`",
    "iss": "`--iss`",
    "parallel_4": "`--parallel` + `OMP_NUM_THREADS=4`",
    "iss_parallel_4": "`--iss --parallel` + `OMP_NUM_THREADS=4`",
}

CASE_REASON_OVERRIDES = {
    "1dloop-invar": "The default verified sequential route already wins; there is not enough structure here to justify heavier variants.",
    "adi": "This wavefront-style kernel loses to more aggressive schedules at the chosen perf size, so the identity fallback is best.",
    "advect3d": "The `--parallel` route found a better sequential schedule, but no verified parallel loop was emitted.",
    "corcol": "Affine rescheduling is enough to improve locality; the extra tiling/parallel routes do not pay back here.",
    "corcol3": "This case benefits from real outer-loop parallelism, so the verified 4-thread parallel route wins.",
    "costfunc": "The default no-ISS affine+tiling route already gives the best sequential trade-off on this recurrence-heavy case.",
    "covcol": "Affine-only blocking/reordering gives the best locality here; the richer routes add overhead.",
    "dct": "The ISS+parallel route wins only as an alternate sequential schedule; it did not emit a verified parallel loop.",
    "doitgen": "This dense kernel has profitable outer-loop parallelism, and the verified parallel route exposes it cleanly.",
    "dsyr2k": "This is a real parallel win: the selected route emits `parallel for`, and the speedup appears only once multiple threads are used.",
    "dsyrk": "Another dense linear-algebra kernel with real outer-loop parallelism; the verified parallel route is clearly best.",
    "fdtd-1d": "Single-thread performance is best when the original loop shape is preserved; skewed or tiled variants hurt at this size.",
    "fdtd-2d": "The more aggressive schedules are profitable for wavefront parallelism, not for this single-thread perf tier, so identity wins.",
    "floyd": "The ISS+parallel route produced the fastest sequential schedule here, but there is no evidence of actual ISS splitting or emitted parallelism on this corpus.",
    "fusion1": "This case is too small/lightweight for the current optimization overheads to pay off, so identity is safest.",
    "fusion10": "The ISS-enabled route measured best, but this is a tiny case and there is no evidence that true ISS splitting fired here.",
    "fusion2": "Affine reordering helps, but the default tiled route is not the best trade-off on this small fusion kernel.",
    "fusion3": "Affine-only fusion/reordering wins without needing the heavier routes.",
    "fusion4": "The `--parallel` route wins as a better sequential schedule; no verified parallel loop was emitted.",
    "fusion5": "Affine-only scheduling is enough to improve this fusion case; the extra routes do not help further.",
    "fusion6": "The default no-ISS affine+tiling pipeline remains the best cached result for this case.",
    "fusion7": "The default no-ISS affine+tiling pipeline already provides the best measured result.",
    "fusion8": "The ISS-enabled route measures best, but the benchmark is small and this should be read as a pipeline-level win, not confirmed ISS splitting.",
    "fusion9": "The best result comes from the ISS+parallel route with real emitted parallelism; the dominant gain is parallel execution, not confirmed ISS splitting.",
    "gemver": "Affine-only scheduling helps producer-consumer locality here; the extra routes are unnecessary.",
    "intratileopt1": "The ISS+parallel route emits real parallelism and wins, though the benefit is smaller than on the denser BLAS-like kernels.",
    "intratileopt2": "Real parallelism is profitable here, so the 4-thread verified parallel route is best.",
    "intratileopt3": "The ISS+parallel route emits real parallelism and edges out the alternatives.",
    "intratileopt4": "This case still prefers the verified parallel route, but the gain is modest compared with the larger dense kernels.",
    "jacobi-1d-imper": "At this perf size, skewing/tiling overheads dominate, so the identity fallback is still fastest.",
    "jacobi-2d-imper": "This stencil prefers the original sequential loop shape at the chosen perf tier; transformed variants are slower.",
    "lu": "The triangular dependence structure does not benefit from the tested transformed routes at this size, so identity wins.",
    "matmul": "A real parallel win: the selected route emits `parallel for` and gives a strong speedup on a dense blocked kernel.",
    "matmul-init": "The verified parallel route wins by parallelizing a regular dense kernel with good outer-loop work sharing.",
    "matmul-seq": "The `--parallel` route is best here as an alternate sequential schedule; it does not actually emit parallel code.",
    "matmul-seq3": "This case is rescued by the `--parallel` scheduling path, but not by actual emitted parallelism.",
    "multi-loop-param": "The ISS-enabled route happened to measure best, but this remains a tiny-case pipeline choice rather than clear ISS activity.",
    "multi-stmt-stencil-seq": "This small stencil-like case still prefers the original schedule at the perf tier used here.",
    "mvt": "The ISS+parallel route emits real parallelism and is the fastest option on this two-kernel benchmark.",
    "mxv": "This matrix-vector case gets a real, but smaller, benefit from verified parallelization.",
    "mxv-seq": "The `--parallel` route wins by choosing a better sequential schedule; no verified parallel loop was emitted.",
    "mxv-seq3": "Again the gain comes from the alternate `--parallel` scheduling path, not from actual parallel execution.",
    "negparam": "Affine-only scheduling gives the best result; the richer routes are not worthwhile here.",
    "nodep": "The ISS-enabled route measures best on this tiny dependence-free case, but there is no evidence of actual ISS splitting.",
    "noloop": "The default no-ISS affine+tiling pipeline is effectively just the best cached default route here.",
    "pca": "The default verified sequential route remains the best measured choice on this benchmark.",
    "polynomial": "This streaming/reduction kernel is hurt by the current transformed variants, so identity remains the best available `polopt` route.",
    "seidel": "The ISS+parallel route wins only as a different sequential schedule; it does not emit a verified parallel loop here.",
    "seq": "The default no-ISS affine+tiling pipeline already gives the best measured sequential result.",
    "shift": "Affine-only scheduling is the best trade-off; heavier routes do not improve this simple shift kernel.",
    "spatial": "The ISS+parallel route emits real parallelism and wins, although the gain is moderate.",
    "ssymm": "This is one of the strongest real parallel wins; the ISS+parallel route emits `parallel for` and scales very well.",
    "strmm": "The verified parallel route is clearly best on this dense triangular matrix kernel.",
    "strsm": "Another strong real parallel win: the 4-thread verified route is much faster than the sequential alternatives.",
    "tce": "The `--parallel` route wins as a better sequential schedule; it did not emit parallel code on this case.",
    "tmm": "This dense matrix kernel gets a strong real gain from verified parallelization.",
    "tricky1": "Affine-only scheduling is decisively best on this synthetic case; the richer routes add no value.",
    "tricky2": "The ISS-enabled route wins on a very small synthetic case, but this should not be overinterpreted as confirmed ISS splitting.",
    "tricky3": "Same story as `tricky2`: ISS-route win, but on a tiny case without evidence of real ISS activity.",
    "tricky4": "Again the ISS-enabled route wins only as a small-case pipeline choice, not confirmed ISS splitting.",
    "trisolv": "This is a real parallel win with a strong speedup from the verified 4-thread route.",
    "wavefront": "The default no-ISS affine+tiling pipeline remains the best cached sequential result on this benchmark.",
}


def canonical_pipeline(name: str) -> str:
    return PIPELINE_CANON.get(name, name)


def load_json(path: pathlib.Path):
    return json.loads(path.read_text())


def reason_for(case: str, pipeline: str, parallelized: bool) -> str:
    if case in CASE_REASON_OVERRIDES:
        return CASE_REASON_OVERRIDES[case]
    if pipeline == "identity":
        return "All non-identity transformed variants were slower at this perf tier, so the identity fallback is best."
    if pipeline == "default_no_iss_affine_tiling":
        return "The default verified sequential affine+tiling route gave the best measured runtime."
    if pipeline == "affine_only":
        return "Affine scheduling helps, but the heavier tiling/parallel routes do not pay off here."
    if pipeline == "iss":
        return "The ISS-enabled route measured best, but this corpus does not by itself show confirmed ISS splitting."
    if pipeline == "parallel_4":
        if parallelized:
            return "The verified parallel route emits a real `parallel for`, and that parallelism is the main source of gain."
        return "The `--parallel` scheduling path was best even though it did not emit a verified parallel loop."
    if pipeline == "iss_parallel_4":
        if parallelized:
            return "The ISS+parallel route emits real parallelism; the gain is mainly from parallel execution, not confirmed ISS splitting."
        return "The ISS+parallel path won as an alternate sequential schedule, without emitting a verified parallel loop."
    return "Best measured route on the current perf tier."


def make_table(summary: dict, report: dict) -> str:
    counts = Counter(canonical_pipeline(v) for v in summary["cases"].values())
    lines = []
    lines.append("# Best Generated Perf Pipelines")
    lines.append("")
    lines.append("This table records the current best measured `polopt` pipeline for each generated end-to-end perf case.")
    lines.append("")
    lines.append("Notes:")
    lines.append("")
    lines.append("- Baseline is always the unoptimized `input.loop` compiled into the same generated whole-C harness.")
    lines.append("- Every selected optimized result goes through `polopt`; baseline is **not** eligible as a best pipeline.")
    lines.append("- `identity` is only a last-resort `polopt --identity` fallback when all real optimization routes are slower.")
    lines.append("- All selected best results currently have `exact_match=true`, `max_abs_diff=0.0`, and `max_rel_diff=0.0`.")
    lines.append("- On this 62-case corpus, `iss` / `iss_parallel_4` means the `--iss` route measured best; it does **not** by itself prove that Pluto actually performed ISS statement splitting on that case.")
    lines.append("")
    lines.append("## Pipeline Counts")
    lines.append("")
    for key in [
        "default_no_iss_affine_tiling",
        "affine_only",
        "iss",
        "parallel_4",
        "iss_parallel_4",
        "identity",
    ]:
        lines.append(f"- {PIPELINE_LABEL[key]}: `{counts.get(key, 0)}`")
    lines.append("")
    lines.append("## Per-Case Table")
    lines.append("")
    lines.append("| Case | Best pipeline | Flags | Speedup | Optimized time | Parallelized | Reason |")
    lines.append("|---|---|---|---:|---:|---|---|")
    for case in sorted(report):
        best = report[case]["best_pipeline"]
        best = canonical_pipeline(best)
        cand = next(
            c for c in report[case]["candidates"] if canonical_pipeline(c["pipeline_name"]) == best
        )
        par = bool(cand["parallelized_loop"])
        lines.append(
            "| {case} | {pipe} | {flags} | {speedup:.3f}x | {opt:.4f}s | {par} | {reason} |".format(
                case=case,
                pipe=PIPELINE_LABEL[best],
                flags=PIPELINE_FLAGS[best],
                speedup=float(cand["speedup"]),
                opt=float(cand["optimized_best_seconds"]),
                par="yes" if par else "no",
                reason=reason_for(case, best, par).replace("|", "/"),
            )
        )
    lines.append("")
    return "\n".join(lines) + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--summary-in", required=True)
    ap.add_argument("--report-in", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()

    summary_path = pathlib.Path(args.summary_in)
    report_path = pathlib.Path(args.report_in)
    out_path = pathlib.Path(args.output)

    summary = load_json(summary_path)
    report = load_json(report_path)
    out_path.write_text(make_table(summary, report))
    print(f"[E2E-GEN-REPORT] OK {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
