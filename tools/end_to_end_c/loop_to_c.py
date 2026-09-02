#!/usr/bin/env python3
from __future__ import annotations

import argparse
import ast
import pathlib
import re


INTEGER_HELPERS_C = r"""static long long polcert_z_div(long long numerator, long long denominator) {
  if (denominator == 0) {
    fputs("PolCert harness: division by zero\n", stderr);
    abort();
  }
  long long quotient = numerator / denominator;
  long long remainder = numerator % denominator;
  if (remainder < 0) {
    quotient += denominator > 0 ? -1 : 1;
  }
  return quotient;
}

static long long polcert_z_mod(long long numerator, long long denominator) {
  if (denominator == 0) {
    fputs("PolCert harness: modulo by zero\n", stderr);
    abort();
  }
  long long remainder = numerator % denominator;
  if (remainder < 0) {
    remainder += denominator > 0 ? denominator : -denominator;
  }
  return remainder;
}
"""


class _LowerIntegerOperators(ast.NodeTransformer):
    def visit_BinOp(self, node: ast.BinOp) -> ast.expr:
        node = self.generic_visit(node)
        if isinstance(node.op, (ast.Div, ast.FloorDiv)):
            return ast.copy_location(
                ast.Call(
                    func=ast.Name(id="polcert_z_div", ctx=ast.Load()),
                    args=[node.left, node.right],
                    keywords=[],
                ),
                node,
            )
        if isinstance(node.op, ast.Mod):
            return ast.copy_location(
                ast.Call(
                    func=ast.Name(id="polcert_z_mod", ctx=ast.Load()),
                    args=[node.left, node.right],
                    keywords=[],
                ),
                node,
            )
        return node


def _rewrite_python_expr(text: str) -> str:
    tree = ast.parse(text, mode="eval")
    lowered = _LowerIntegerOperators().visit(tree)
    ast.fix_missing_locations(lowered)
    return ast.unparse(lowered.body)


def rewrite_integer_expr(text: str) -> str:
    """Lower Loop integer division and modulo to Rocq-Z-compatible helpers."""
    return _rewrite_python_expr(text)


def rewrite_integer_test(text: str) -> str:
    python = text.replace("&&", " and ").replace("||", " or ")
    python = re.sub(r"(?<![=!<>])!(?!=)", " not ", python)
    python = re.sub(r"\btrue\b", "True", python)
    python = re.sub(r"\bfalse\b", "False", python)
    lowered = _rewrite_python_expr(python)
    lowered = re.sub(r"\band\b", "&&", lowered)
    lowered = re.sub(r"\bor\b", "||", lowered)
    lowered = re.sub(r"\bnot\s+", "!", lowered)
    lowered = re.sub(r"\bTrue\b", "1", lowered)
    return re.sub(r"\bFalse\b", "0", lowered)


def rewrite_array_subscripts(line: str) -> str:
    out: list[str] = []
    cursor = 0
    while cursor < len(line):
        if line[cursor] != "[":
            out.append(line[cursor])
            cursor += 1
            continue
        depth = 1
        end = cursor + 1
        while end < len(line) and depth:
            if line[end] == "[":
                depth += 1
            elif line[end] == "]":
                depth -= 1
            end += 1
        if depth:
            raise ValueError(f"unterminated array subscript: {line!r}")
        inner = line[cursor + 1 : end - 1]
        out.append(f"[{rewrite_integer_expr(inner)}]")
        cursor = end
    return "".join(out)


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
        or stripped.startswith("innermost parallel for ")
        or stripped.startswith("vector for ")
        or stripped.startswith("for ")
    ):
        is_parallel = stripped.startswith("parallel for ")
        is_vector = stripped.startswith(("vector for ", "innermost parallel for "))
        prefix = (
            "parallel for "
            if is_parallel
            else "innermost parallel for "
            if stripped.startswith("innermost parallel for ")
            else "vector for "
            if is_vector
            else "for "
        )
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
        lb = rewrite_integer_expr(lb)
        ub = rewrite_integer_expr(ub)
        step = rewrite_integer_expr(step)
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
        return [f"{indent}if ({rewrite_integer_test(cond[:-1].strip())}) {{"]

    return [rewrite_array_subscripts(line)]


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
