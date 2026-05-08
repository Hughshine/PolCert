#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib


def split_top_level_commas(text: str) -> list[str]:
    depth = 0
    bracket = 0
    parts: list[str] = []
    start = 0
    for i, ch in enumerate(text):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "[":
            bracket += 1
        elif ch == "]":
            bracket -= 1
        elif ch == "," and depth == 0 and bracket == 0:
            parts.append(text[start:i].strip())
            start = i + 1
    parts.append(text[start:].strip())
    return parts


def parse_int_literal(text: str) -> int | None:
    try:
        return int(text.strip(), 10)
    except ValueError:
        return None


def transpile_line(line: str) -> list[str]:
    stripped = line.strip()
    if not stripped:
        return [""]
    if stripped.startswith("context("):
        return []
    if stripped == "skip;":
        return [line[: len(line) - len(line.lstrip())] + ";"]

    indent = line[: len(line) - len(line.lstrip())]

    if (
        stripped.startswith("parallel for ")
        or stripped.startswith("vector for ")
        or stripped.startswith("for ")
    ):
        is_parallel = stripped.startswith("parallel for ")
        is_vector = stripped.startswith("vector for ")
        prefix = "parallel for " if is_parallel else "vector for " if is_vector else "for "
        rest = stripped[len(prefix) :]
        marker = " in range("
        if marker not in rest or not rest.endswith(") {"):
            raise ValueError(f"unsupported loop syntax: {line!r}")
        var, tail = rest.split(marker, 1)
        inner = tail[:-3]
        parts = split_top_level_commas(inner)
        if len(parts) == 2:
            lb, ub = parts
            step = "1"
        elif len(parts) == 3:
            lb, ub, step = parts
        else:
            raise ValueError(f"unsupported range arity: {line!r}")
        step_lit = parse_int_literal(step)
        if step_lit == 0:
            raise ValueError(f"zero range step: {line!r}")
        if step_lit is not None and step_lit < 0:
            cond = f"{var.strip()} > {ub}"
            incr = f"--{var.strip()}" if step_lit == -1 else f"{var.strip()} += {step}"
        else:
            cond = f"{var.strip()} < {ub}"
            incr = f"++{var.strip()}" if step == "1" else f"{var.strip()} += {step}"
        loop_line = f"{indent}for (long long {var.strip()} = {lb}; {cond}; {incr}) {{"
        if is_parallel:
            return [f"{indent}#pragma omp parallel for", loop_line]
        if is_vector:
            return [f"{indent}#pragma omp simd", loop_line]
        return [loop_line]

    if stripped.startswith("if "):
        cond = stripped[3:]
        if not cond.endswith("{"):
            raise ValueError(f"unsupported if syntax: {line!r}")
        return [f"{indent}if {cond}"]

    return [line]


def transpile_loop_text(text: str) -> str:
    out: list[str] = []
    for line in text.splitlines():
        out.extend(transpile_line(line))
    return "\n".join(out).rstrip() + "\n"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("src")
    ap.add_argument("dst", nargs="?")
    args = ap.parse_args()

    src = pathlib.Path(args.src)
    text = src.read_text()
    lowered = transpile_loop_text(text)
    if args.dst is None:
        print(lowered, end="")
    else:
        pathlib.Path(args.dst).write_text(lowered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
