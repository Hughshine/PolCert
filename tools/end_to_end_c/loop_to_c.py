#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib


def split_top_level_comma(text: str) -> tuple[str, str]:
    depth = 0
    bracket = 0
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
            return text[:i].strip(), text[i + 1 :].strip()
    raise ValueError(f"could not split top-level range arguments: {text!r}")


def transpile_line(line: str) -> list[str]:
    stripped = line.strip()
    if not stripped:
        return [""]
    if stripped.startswith("context("):
        return []
    if stripped == "skip;":
        return [line[: len(line) - len(line.lstrip())] + ";"]

    indent = line[: len(line) - len(line.lstrip())]

    if stripped.startswith("parallel for ") or stripped.startswith("for "):
        is_parallel = stripped.startswith("parallel for ")
        prefix = "parallel for " if is_parallel else "for "
        rest = stripped[len(prefix) :]
        marker = " in range("
        if marker not in rest or not rest.endswith(") {"):
            raise ValueError(f"unsupported loop syntax: {line!r}")
        var, tail = rest.split(marker, 1)
        inner = tail[:-3]
        lb, ub = split_top_level_comma(inner)
        loop_line = f"{indent}for (long long {var.strip()} = {lb}; {var.strip()} < {ub}; ++{var.strip()}) {{"
        if is_parallel:
            return [f"{indent}#pragma omp parallel for", loop_line]
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
