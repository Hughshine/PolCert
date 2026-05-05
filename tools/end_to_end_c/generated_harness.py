#!/usr/bin/env python3
from __future__ import annotations

import ast
import dataclasses
import hashlib
import json
import pathlib
import re
from typing import Iterable

from loop_to_c import split_top_level_comma, transpile_loop_text
from runner_common import loop_requires_openmp


LOOP_RE = re.compile(
    r"^\s*(?:(?:parallel|vector)\s+)?for\s+([A-Za-z_][A-Za-z0-9_]*)\s+in\s+range\((.*)\)\s*\{\s*$"
)
TOKEN_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")
KEYWORDS = {"context", "for", "in", "range", "if", "skip", "parallel", "vector"}
MATH_NAMES = {"sqrt", "ceil", "floor", "max", "min", "abs"}
CASE_VALUE_OVERRIDES: dict[str, dict[str, int]] = {
    "advect3d": {"nx": 20, "ny": 20, "nz": 20},
    "negparam": {"n": 4},
    "tce": {"N": 6},
    "doitgen": {"N": 12},
    "pca": {"m": 32, "n": 64},
}
DEFAULT_TIER = "smoke"


@dataclasses.dataclass(frozen=True)
class ArrayAccess:
    name: str
    exprs: tuple[str, ...]
    start: int
    end: int


@dataclasses.dataclass(frozen=True)
class ArrayDim:
    lower: int
    upper: int
    shift: int
    extent: int


@dataclasses.dataclass(frozen=True)
class HarnessInfo:
    case_name: str
    params: dict[str, int]
    arrays: dict[str, tuple[ArrayDim, ...]]
    scalars: tuple[str, ...]
    functions: tuple[str, ...]
    baseline_kernel: str
    optimized_kernel: str
    openmp: bool


def default_param_value(max_rank: int) -> int:
    if max_rank >= 4:
        return 6
    if max_rank == 3:
        return 20
    if max_rank == 2:
        return 96
    return 4096


def load_param_tiers(path: pathlib.Path) -> dict[str, dict[str, dict[str, int]]]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text())
    result: dict[str, dict[str, dict[str, int]]] = {}
    for case_name, tier_map in data.items():
        result[case_name] = {}
        for tier, params in tier_map.items():
            result[case_name][tier] = {name: int(value) for name, value in params.items()}
    return result


def parse_context_params(loop_text: str) -> list[str]:
    for line in loop_text.splitlines():
        stripped = line.strip()
        if stripped.startswith("context(") and stripped.endswith(");"):
            inner = stripped[len("context(") : -2].strip()
            if not inner:
                return []
            return [part.strip() for part in inner.split(",") if part.strip()]
    return []


def scan_array_accesses(text: str) -> list[ArrayAccess]:
    accesses: list[ArrayAccess] = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == '"' or ch == "'":
            quote = ch
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == quote:
                    i += 1
                    break
                i += 1
            continue
        if ch.isalpha() or ch == "_":
            start = i
            i += 1
            while i < n and (text[i].isalnum() or text[i] == "_"):
                i += 1
            name = text[start:i]
            j = i
            exprs: list[str] = []
            while j < n and text[j] == "[":
                depth = 1
                expr_start = j + 1
                j += 1
                while j < n and depth > 0:
                    if text[j] == "[":
                        depth += 1
                    elif text[j] == "]":
                        depth -= 1
                    j += 1
                exprs.append(text[expr_start : j - 1].strip())
            if exprs:
                accesses.append(ArrayAccess(name=name, exprs=tuple(exprs), start=start, end=j))
                i = j
                continue
        i += 1
    return accesses


def interval_union(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return min(a[0], b[0]), max(a[1], b[1])


def div_candidates(lo1: int, hi1: int, lo2: int, hi2: int) -> tuple[int, int]:
    vals: list[int] = []
    for a in (lo1, hi1):
        for b in (lo2, hi2):
            if b == 0:
                continue
            vals.append(int(a / b))
    if not vals:
        raise ValueError("division by zero while estimating bounds")
    return min(vals), max(vals)


def eval_interval(expr: str, env: dict[str, tuple[int, int]]) -> tuple[int, int]:
    tree = ast.parse(expr, mode="eval")

    def visit(node: ast.AST) -> tuple[int, int]:
        if isinstance(node, ast.Expression):
            return visit(node.body)
        if isinstance(node, ast.Constant):
            if not isinstance(node.value, (int, float)):
                raise ValueError(f"unsupported constant in expression: {expr!r}")
            value = int(node.value)
            return value, value
        if isinstance(node, ast.Name):
            if node.id not in env:
                raise ValueError(f"unknown identifier {node.id!r} in expression {expr!r}")
            return env[node.id]
        if isinstance(node, ast.UnaryOp):
            lo, hi = visit(node.operand)
            if isinstance(node.op, ast.USub):
                return -hi, -lo
            if isinstance(node.op, ast.UAdd):
                return lo, hi
            raise ValueError(f"unsupported unary operator in expression: {expr!r}")
        if isinstance(node, ast.BinOp):
            lo1, hi1 = visit(node.left)
            lo2, hi2 = visit(node.right)
            if isinstance(node.op, ast.Add):
                return lo1 + lo2, hi1 + hi2
            if isinstance(node.op, ast.Sub):
                return lo1 - hi2, hi1 - lo2
            if isinstance(node.op, ast.Mult):
                vals = [lo1 * lo2, lo1 * hi2, hi1 * lo2, hi1 * hi2]
                return min(vals), max(vals)
            if isinstance(node.op, (ast.Div, ast.FloorDiv)):
                return div_candidates(lo1, hi1, lo2, hi2)
            raise ValueError(f"unsupported binary operator in expression: {expr!r}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            fn = node.func.id
            args = [visit(arg) for arg in node.args]
            if fn == "max":
                return max(lo for lo, _ in args), max(hi for _, hi in args)
            if fn == "min":
                return min(lo for lo, _ in args), min(hi for _, hi in args)
            if fn in {"ceild", "floord"}:
                if len(args) != 2:
                    raise ValueError(f"unsupported arity for {fn} in {expr!r}")
                return div_candidates(args[0][0], args[0][1], args[1][0], args[1][1])
            raise ValueError(f"unsupported call {fn} in expression: {expr!r}")
        raise ValueError(f"unsupported expression form: {expr!r}")

    return visit(tree)


def collect_var_ranges(loop_texts: Iterable[str], params: dict[str, int]) -> dict[str, tuple[int, int]]:
    env: dict[str, tuple[int, int]] = {name: (value, value) for name, value in params.items()}
    for loop_text in loop_texts:
        for line in loop_text.splitlines():
            match = LOOP_RE.match(line)
            if not match:
                continue
            var = match.group(1)
            lb, ub = split_top_level_comma(match.group(2))
            lb_lo, lb_hi = eval_interval(lb, env)
            ub_lo, ub_hi = eval_interval(ub, env)
            loop_range = (lb_lo, max(lb_hi, ub_hi - 1))
            if var in env:
                env[var] = interval_union(env[var], loop_range)
            else:
                env[var] = loop_range
    return env


def build_array_shapes(loop_texts: Iterable[str], env: dict[str, tuple[int, int]]) -> dict[str, tuple[ArrayDim, ...]]:
    shapes: dict[str, list[tuple[int, int]]] = {}
    for loop_text in loop_texts:
        for access in scan_array_accesses(loop_text):
            bounds = [eval_interval(expr, env) for expr in access.exprs]
            current = shapes.setdefault(access.name, [(lo, hi) for lo, hi in bounds])
            for idx, bound in enumerate(bounds):
                if idx >= len(current):
                    current.append(bound)
                else:
                    current[idx] = interval_union(current[idx], bound)
    result: dict[str, tuple[ArrayDim, ...]] = {}
    for name, bounds in shapes.items():
        dims: list[ArrayDim] = []
        for lower, upper in bounds:
            pad = 2
            shift = pad - lower
            extent = (upper - lower + 1) + 2 * pad
            dims.append(ArrayDim(lower=lower, upper=upper, shift=shift, extent=extent))
        result[name] = tuple(dims)
    return result


def choose_params(case_name: str, params: list[str], max_rank: int) -> dict[str, int]:
    base = default_param_value(max_rank)
    values = {name: base for name in params}
    values.update(CASE_VALUE_OVERRIDES.get(case_name, {}))
    return values


def choose_params_for_tier(
    case_name: str,
    params: list[str],
    max_rank: int,
    *,
    tier: str = DEFAULT_TIER,
    tier_overrides: dict[str, dict[str, dict[str, int]]] | None = None,
) -> dict[str, int]:
    values = choose_params(case_name, params, max_rank)
    if tier_overrides is not None:
        values.update(tier_overrides.get(case_name, {}).get(tier, {}))
    return values


def collect_loop_vars(loop_texts: Iterable[str]) -> set[str]:
    vars_: set[str] = set()
    for loop_text in loop_texts:
        for line in loop_text.splitlines():
            match = LOOP_RE.match(line)
            if match:
                vars_.add(match.group(1))
    return vars_


def collect_scalar_names(loop_texts: Iterable[str], params: set[str], loop_vars: set[str], arrays: set[str]) -> tuple[str, ...]:
    names: set[str] = set()
    for loop_text in loop_texts:
        names.update(TOKEN_RE.findall(loop_text))
    scalars = sorted(
        name
        for name in names
        if name not in KEYWORDS
        and name not in MATH_NAMES
        and name not in params
        and name not in loop_vars
        and name not in arrays
        and not name.isupper()
    )
    return tuple(scalars)


def collect_called_functions(loop_texts: Iterable[str]) -> tuple[str, ...]:
    names: set[str] = set()
    for loop_text in loop_texts:
        for match in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(", loop_text):
            name = match.group(1)
            if name not in KEYWORDS and name != "range":
                names.add(name)
    return tuple(sorted(names))


def scalar_initializer(name: str, params: dict[str, int]) -> str:
    suffix = name.split("float_", 1)[1] if name.startswith("float_") else None
    if suffix and suffix in params:
        return f"(double){suffix}"
    if name == "eps":
        return "0.1"
    if name in {"alpha", "beta"}:
        return "1.0"
    digest = hashlib.sha256(name.encode("utf-8")).digest()[0]
    value = 0.25 + (digest % 11) / 8.0
    return f"{value:.6f}"


def rewrite_array_accesses(c_text: str, arrays: dict[str, tuple[ArrayDim, ...]]) -> str:
    parts: list[str] = []
    cursor = 0
    for access in scan_array_accesses(c_text):
        parts.append(c_text[cursor : access.start])
        dims = arrays.get(access.name)
        if dims is None or len(dims) != len(access.exprs):
            parts.append(c_text[access.start : access.end])
        else:
            rewritten = access.name
            for expr, dim in zip(access.exprs, dims):
                rewritten += f"[(({expr}) + {dim.shift})]"
            parts.append(rewritten)
        cursor = access.end
    parts.append(c_text[cursor:])
    return "".join(parts)


def render_array_decls(arrays: dict[str, tuple[ArrayDim, ...]]) -> str:
    lines: list[str] = []
    for name, dims in sorted(arrays.items()):
        suffix = "".join(f"[{dim.extent}]" for dim in dims)
        lines.append(f"static double {name}{suffix};")
    return "\n".join(lines) + ("\n" if lines else "")


def render_scalar_decls(scalars: Iterable[str], params: dict[str, int]) -> str:
    lines = [f"static double {name} = {scalar_initializer(name, params)};" for name in scalars]
    return "\n".join(lines) + ("\n" if lines else "")


def render_param_decls(params: dict[str, int]) -> str:
    return "\n".join(f"static const long long {name} = {value};" for name, value in sorted(params.items())) + (
        "\n" if params else ""
    )


def render_array_loops(
    name: str,
    dims: tuple[ArrayDim, ...],
    body_fn,
) -> list[str]:
    indices = [f"__i{depth}" for depth in range(len(dims))]
    lines: list[str] = []
    indent = ""
    for idx, dim in zip(indices, dims):
        lines.append(f"{indent}for (long long {idx} = 0; {idx} < {dim.extent}; ++{idx}) {{")
        indent += "  "
    lines.extend(body_fn(indent, indices))
    for depth in range(len(dims)):
        indent = indent[:-2]
        lines.append(f"{indent}}}")
    return lines


def render_init_function(arrays: dict[str, tuple[ArrayDim, ...]], scalars: tuple[str, ...], params: dict[str, int]) -> str:
    lines = ["static void init_data(void) {"]
    for idx, name in enumerate(scalars):
        lines.append(f"  {name} = {scalar_initializer(name, params)};")
        if name.startswith("float_") and name.split('float_', 1)[1] in params:
            continue
    for seed, (name, dims) in enumerate(sorted(arrays.items()), start=1):
        def body(indent: str, indices: list[str]) -> list[str]:
            linear = " + ".join(f"({i} + {pos + 1}) * {17 + pos}" for pos, i in enumerate(indices)) or "0"
            index = "".join(f"[{idx}]" for idx in indices)
            return [f"{indent}{name}{index} = ((double)(({linear} + {seed}) % 97) / 13.0);"]

        lines.extend(f"  {line}" for line in render_array_loops(name, dims, body))
    lines.append("}")
    return "\n".join(lines) + "\n"


def render_checksum_function(arrays: dict[str, tuple[ArrayDim, ...]], scalars: tuple[str, ...]) -> str:
    lines = ["static double checksum(void) {", "  double acc = 0.0;"]
    for idx, name in enumerate(scalars, start=1):
        lines.append(f"  acc += {name} * {1.0 + idx / 16.0:.6f};")
    for seed, (name, dims) in enumerate(sorted(arrays.items()), start=1):
        def body(indent: str, indices: list[str]) -> list[str]:
            index = "".join(f"[{idx}]" for idx in indices)
            return [f"{indent}acc += {name}{index} * {1.0 + seed / 32.0:.6f};"]

        lines.extend(f"  {line}" for line in render_array_loops(name, dims, body))
    lines.extend(["  return acc;", "}"])
    return "\n".join(lines) + "\n"


def render_helper_functions(functions: tuple[str, ...], arrays: dict[str, tuple[ArrayDim, ...]]) -> str:
    lines: list[str] = []
    if "my_sqrt_array" in functions and "stddev" in arrays and len(arrays["stddev"]) == 1:
        shift = arrays["stddev"][0].shift
        lines.extend(
            [
                "static double my_sqrt_array(double *arr, long long idx) {",
                f"  return sqrt(arr[idx + {shift}]);",
                "}",
            ]
        )
    return "\n".join(lines) + ("\n" if lines else "")


def render_program_source(info: HarnessInfo, *, optimized: bool) -> str:
    kernel = info.optimized_kernel if optimized else info.baseline_kernel
    lines = [
        "#include <math.h>",
        "#include <stdio.h>",
        "#include <stdlib.h>",
        "",
        "#ifndef max",
        "#define max(x, y) ((x) > (y) ? (x) : (y))",
        "#endif",
        "#ifndef min",
        "#define min(x, y) ((x) < (y) ? (x) : (y))",
        "#endif",
        "",
        render_param_decls(info.params).rstrip(),
        render_array_decls(info.arrays).rstrip(),
        render_scalar_decls(info.scalars, info.params).rstrip(),
        render_helper_functions(info.functions, info.arrays).rstrip(),
        render_init_function(info.arrays, info.scalars, info.params).rstrip(),
        render_checksum_function(info.arrays, info.scalars).rstrip(),
        "int main(void) {",
        "  init_data();",
        kernel.rstrip(),
        '  printf("%.17g\\n", checksum());',
        "  return 0;",
        "}",
        "",
    ]
    return "\n".join(part for part in lines if part != "\n") + "\n"


def build_harness(
    case_name: str,
    input_loop: str,
    optimized_loop: str,
    *,
    tier: str = DEFAULT_TIER,
    tier_overrides: dict[str, dict[str, dict[str, int]]] | None = None,
) -> HarnessInfo:
    accesses = scan_array_accesses(input_loop)
    max_rank = max((len(access.exprs) for access in accesses), default=0)
    params_list = parse_context_params(input_loop)
    params = choose_params_for_tier(
        case_name,
        params_list,
        max_rank,
        tier=tier,
        tier_overrides=tier_overrides,
    )
    env = collect_var_ranges([input_loop], params)
    arrays = build_array_shapes([input_loop], env)
    loop_vars = collect_loop_vars([input_loop])
    functions = collect_called_functions([input_loop, optimized_loop])
    scalars = tuple(
        name
        for name in collect_scalar_names([input_loop], set(params), loop_vars, set(arrays))
        if name not in functions
    )
    baseline_kernel = rewrite_array_accesses(transpile_loop_text(input_loop), arrays)
    optimized_kernel = rewrite_array_accesses(transpile_loop_text(optimized_loop), arrays)
    openmp = loop_requires_openmp(optimized_loop) or loop_requires_openmp(input_loop)
    return HarnessInfo(
        case_name=case_name,
        params=params,
        arrays=arrays,
        scalars=scalars,
        functions=functions,
        baseline_kernel=baseline_kernel,
        optimized_kernel=optimized_kernel,
        openmp=openmp,
    )
