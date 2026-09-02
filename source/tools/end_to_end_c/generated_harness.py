#!/usr/bin/env python3
from __future__ import annotations

import ast
import dataclasses
import hashlib
import json
import pathlib
import re
from typing import Iterable

from loop_to_c import INTEGER_HELPERS_C, split_top_level_commas, transpile_loop_text
from runner_common import loop_requires_openmp


LOOP_RE = re.compile(
    r"^\s*(?:(?:parallel|vector|innermost\s+parallel)\s+)?for\s+"
    r"([A-Za-z_][A-Za-z0-9_]*)\s+in\s+range\((.*)\)\s*\{\s*$"
)
TOKEN_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")
KEYWORDS = {
    "context", "for", "in", "range", "if", "skip", "parallel", "vector",
    "innermost",
}
MATH_NAMES = {"sqrt", "ceil", "floor", "max", "min", "abs"}
CASE_VALUE_OVERRIDES: dict[str, dict[str, int]] = {
    "advect3d": {"nx": 20, "ny": 20, "nz": 20},
    "adi": {"T": 2, "N": 16},
    "negparam": {"n": 4},
    "strsm": {"N": 12},
    "tce": {"N": 6},
    "doitgen": {"N": 12},
    "pca": {"m": 32, "n": 64},
    "trisolv": {"N": 12},
}
DEFAULT_TIER = "smoke"

STATE_DIGEST_HELPERS_C = r"""typedef struct {
  unsigned char data[64];
  unsigned int datalen;
  unsigned long long bitlen;
  unsigned int state[8];
} polcert_sha256_ctx;

static unsigned int polcert_rotr32(unsigned int value, unsigned int amount) {
  return (value >> amount) | (value << (32U - amount));
}

static void polcert_sha256_transform(polcert_sha256_ctx *ctx) {
  static const unsigned int k[64] = {
    0x428a2f98U,0x71374491U,0xb5c0fbcfU,0xe9b5dba5U,0x3956c25bU,0x59f111f1U,0x923f82a4U,0xab1c5ed5U,
    0xd807aa98U,0x12835b01U,0x243185beU,0x550c7dc3U,0x72be5d74U,0x80deb1feU,0x9bdc06a7U,0xc19bf174U,
    0xe49b69c1U,0xefbe4786U,0x0fc19dc6U,0x240ca1ccU,0x2de92c6fU,0x4a7484aaU,0x5cb0a9dcU,0x76f988daU,
    0x983e5152U,0xa831c66dU,0xb00327c8U,0xbf597fc7U,0xc6e00bf3U,0xd5a79147U,0x06ca6351U,0x14292967U,
    0x27b70a85U,0x2e1b2138U,0x4d2c6dfcU,0x53380d13U,0x650a7354U,0x766a0abbU,0x81c2c92eU,0x92722c85U,
    0xa2bfe8a1U,0xa81a664bU,0xc24b8b70U,0xc76c51a3U,0xd192e819U,0xd6990624U,0xf40e3585U,0x106aa070U,
    0x19a4c116U,0x1e376c08U,0x2748774cU,0x34b0bcb5U,0x391c0cb3U,0x4ed8aa4aU,0x5b9cca4fU,0x682e6ff3U,
    0x748f82eeU,0x78a5636fU,0x84c87814U,0x8cc70208U,0x90befffaU,0xa4506cebU,0xbef9a3f7U,0xc67178f2U
  };
  unsigned int m[64];
  unsigned int a,b,c,d,e,f,g,h,t1,t2;
  unsigned int i,j;
  for (i = 0, j = 0; i < 16; ++i, j += 4) {
    m[i] = ((unsigned int)ctx->data[j] << 24)
      | ((unsigned int)ctx->data[j + 1] << 16)
      | ((unsigned int)ctx->data[j + 2] << 8)
      | (unsigned int)ctx->data[j + 3];
  }
  for (; i < 64; ++i) {
    unsigned int s0 = polcert_rotr32(m[i - 15], 7) ^ polcert_rotr32(m[i - 15], 18) ^ (m[i - 15] >> 3);
    unsigned int s1 = polcert_rotr32(m[i - 2], 17) ^ polcert_rotr32(m[i - 2], 19) ^ (m[i - 2] >> 10);
    m[i] = m[i - 16] + s0 + m[i - 7] + s1;
  }
  a=ctx->state[0]; b=ctx->state[1]; c=ctx->state[2]; d=ctx->state[3];
  e=ctx->state[4]; f=ctx->state[5]; g=ctx->state[6]; h=ctx->state[7];
  for (i = 0; i < 64; ++i) {
    unsigned int s1 = polcert_rotr32(e, 6) ^ polcert_rotr32(e, 11) ^ polcert_rotr32(e, 25);
    unsigned int ch = (e & f) ^ ((~e) & g);
    unsigned int s0 = polcert_rotr32(a, 2) ^ polcert_rotr32(a, 13) ^ polcert_rotr32(a, 22);
    unsigned int maj = (a & b) ^ (a & c) ^ (b & c);
    t1 = h + s1 + ch + k[i] + m[i];
    t2 = s0 + maj;
    h=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
  }
  ctx->state[0]+=a; ctx->state[1]+=b; ctx->state[2]+=c; ctx->state[3]+=d;
  ctx->state[4]+=e; ctx->state[5]+=f; ctx->state[6]+=g; ctx->state[7]+=h;
}

static void polcert_sha256_init(polcert_sha256_ctx *ctx) {
  ctx->datalen=0; ctx->bitlen=0;
  ctx->state[0]=0x6a09e667U; ctx->state[1]=0xbb67ae85U;
  ctx->state[2]=0x3c6ef372U; ctx->state[3]=0xa54ff53aU;
  ctx->state[4]=0x510e527fU; ctx->state[5]=0x9b05688cU;
  ctx->state[6]=0x1f83d9abU; ctx->state[7]=0x5be0cd19U;
}

static void polcert_sha256_update(polcert_sha256_ctx *ctx, const unsigned char *data, unsigned int len) {
  unsigned int i;
  for (i = 0; i < len; ++i) {
    ctx->data[ctx->datalen++] = data[i];
    if (ctx->datalen == 64) {
      polcert_sha256_transform(ctx);
      ctx->bitlen += 512;
      ctx->datalen = 0;
    }
  }
}

static void polcert_sha256_final(polcert_sha256_ctx *ctx, unsigned char hash[32]) {
  unsigned int i = ctx->datalen;
  ctx->data[i++] = 0x80;
  if (i > 56) {
    while (i < 64) ctx->data[i++] = 0;
    polcert_sha256_transform(ctx);
    i = 0;
  }
  while (i < 56) ctx->data[i++] = 0;
  ctx->bitlen += (unsigned long long)ctx->datalen * 8ULL;
  for (i = 0; i < 8; ++i) ctx->data[63 - i] = (unsigned char)(ctx->bitlen >> (8U * i));
  polcert_sha256_transform(ctx);
  for (i = 0; i < 4; ++i) {
    hash[i]      = (unsigned char)(ctx->state[0] >> (24U - 8U * i));
    hash[i + 4]  = (unsigned char)(ctx->state[1] >> (24U - 8U * i));
    hash[i + 8]  = (unsigned char)(ctx->state[2] >> (24U - 8U * i));
    hash[i + 12] = (unsigned char)(ctx->state[3] >> (24U - 8U * i));
    hash[i + 16] = (unsigned char)(ctx->state[4] >> (24U - 8U * i));
    hash[i + 20] = (unsigned char)(ctx->state[5] >> (24U - 8U * i));
    hash[i + 24] = (unsigned char)(ctx->state[6] >> (24U - 8U * i));
    hash[i + 28] = (unsigned char)(ctx->state[7] >> (24U - 8U * i));
  }
}

static void polcert_observe_double(polcert_sha256_ctx *ctx, unsigned long long *count, double value) {
  unsigned long long bits;
  unsigned char encoded[8];
  unsigned int i;
  if (!isfinite(value)) {
    fputs("PolCert harness: non-finite modeled value\n", stderr);
    exit(3);
  }
  if (sizeof(double) != 8 || sizeof(unsigned int) != 4) {
    fputs("PolCert harness: unsupported numeric representation\n", stderr);
    exit(4);
  }
  memcpy(&bits, &value, 8);
  for (i = 0; i < 8; ++i) encoded[i] = (unsigned char)(bits >> (8U * i));
  polcert_sha256_update(ctx, encoded, 8);
  *count += 1;
}
"""


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
            vals.append(a // b)
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
            bounds = split_top_level_commas(match.group(2))
            if len(bounds) not in (2, 3):
                raise ValueError(
                    f"unsupported range arity while estimating bounds: {line!r}"
                )
            lb, ub = bounds[:2]
            lb_lo, lb_hi = eval_interval(lb, env)
            ub_lo, ub_hi = eval_interval(ub, env)
            if len(bounds) == 3:
                step_lo, step_hi = eval_interval(bounds[2], env)
                if step_lo <= 0 <= step_hi:
                    raise ValueError(
                        f"zero or sign-ambiguous range step while estimating bounds: {line!r}"
                    )
            else:
                step_lo = step_hi = 1
            if step_hi < 0:
                loop_range = (
                    min(lb_lo, ub_lo + 1),
                    max(lb_hi, ub_hi + 1),
                )
            else:
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
            return [
                f"{indent}{name}{index} = "
                f"((double)((({linear} + {seed}) % 97) + 1) / 13.0);"
            ]

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
            linear = indices[0] if indices else "0"
            for dimension, idx in zip(dims[1:], indices[1:]):
                linear = f"(({linear}) * {dimension.extent} + {idx})"
            weight = f"(1.0 + ((double)(({linear}) + {seed}) / 1024.0))"
            return [f"{indent}acc += {name}{index} * {weight};"]

        lines.extend(f"  {line}" for line in render_array_loops(name, dims, body))
    lines.extend(["  return acc;", "}"])
    return "\n".join(lines) + "\n"


def render_state_digest_function(
    arrays: dict[str, tuple[ArrayDim, ...]], scalars: tuple[str, ...]
) -> str:
    lines = [
        "static void print_modeled_state_digest(void) {",
        "  polcert_sha256_ctx ctx;",
        "  unsigned char digest[32];",
        "  unsigned long long count = 0;",
        "  unsigned int digest_index;",
        "  polcert_sha256_init(&ctx);",
    ]
    for name in scalars:
        lines.append(f"  polcert_observe_double(&ctx, &count, (double){name});")
    for name, dims in sorted(arrays.items()):
        def body(indent: str, indices: list[str]) -> list[str]:
            index = "".join(f"[{idx}]" for idx in indices)
            return [
                f"{indent}polcert_observe_double(&ctx, &count, "
                f"(double){name}{index});"
            ]

        lines.extend(f"  {line}" for line in render_array_loops(name, dims, body))
    lines.extend(
        [
            "  polcert_sha256_final(&ctx, digest);",
            '  printf("observed_value_count=%llu\\nstate_sha256=", count);',
            '  for (digest_index = 0; digest_index < 32; ++digest_index) printf("%02x", digest[digest_index]);',
            '  putchar(\'\\n\');',
            "}",
        ]
    )
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


def render_program_source(
    info: HarnessInfo, *, optimized: bool, state_digest_output: bool = False
) -> str:
    kernel = info.optimized_kernel if optimized else info.baseline_kernel
    lines = [
        "#include <math.h>",
        "#include <limits.h>",
        "#include <stdio.h>",
        "#include <stdlib.h>",
        "#include <string.h>",
        "",
        "#ifndef max",
        "#define max(x, y) ((x) > (y) ? (x) : (y))",
        "#endif",
        "#ifndef min",
        "#define min(x, y) ((x) < (y) ? (x) : (y))",
        "#endif",
        "",
        INTEGER_HELPERS_C.rstrip(),
        STATE_DIGEST_HELPERS_C.rstrip() if state_digest_output else "",
        render_param_decls(info.params).rstrip(),
        render_array_decls(info.arrays).rstrip(),
        render_scalar_decls(info.scalars, info.params).rstrip(),
        render_helper_functions(info.functions, info.arrays).rstrip(),
        render_init_function(info.arrays, info.scalars, info.params).rstrip(),
        (
            render_state_digest_function(info.arrays, info.scalars).rstrip()
            if state_digest_output
            else render_checksum_function(info.arrays, info.scalars).rstrip()
        ),
        "int main(void) {",
        "  init_data();",
        kernel.rstrip(),
        (
            "  print_modeled_state_digest();"
            if state_digest_output
            else '  printf("%.17g\\n", checksum());'
        ),
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
