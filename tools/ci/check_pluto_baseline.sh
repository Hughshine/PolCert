#!/usr/bin/env bash
set -euo pipefail

cd /polcert

# shellcheck disable=SC1091
source /polcert/tools/ci/pluto-baseline.env

if [[ "$PLUTO_IMAGE" == *:latest ]]; then
  echo "[ci] WARNING: PLUTO_IMAGE still uses :latest; publish and pin a versioned image tag such as ${PLUTO_VERSIONED_IMAGE:-<set PLUTO_VERSIONED_IMAGE>}" >&2
fi

require_match() {
  local name="$1"
  local expected="$2"
  local actual="$3"
  if [[ "$actual" != "$expected" ]]; then
    echo "[ci] Pluto baseline mismatch for $name" >&2
    echo "[ci]   expected: $expected" >&2
    echo "[ci]   actual:   $actual" >&2
    exit 1
  fi
}

baked_values=(
  "${POLCERT_PLUTO_IMAGE:-}"
  "${POLCERT_PLUTO_GIT_REMOTE:-}"
  "${POLCERT_PLUTO_GIT_COMMIT:-}"
)

buggy_baked_values=(
  "${POLCERT_BUGGY_PLUTO_GIT_REMOTE:-}"
  "${POLCERT_BUGGY_PLUTO_GIT_COMMIT:-}"
  "${POLCERT_BUGGY_PLUTO:-}"
  "${POLCERT_BUGGY_POLYCC:-}"
)

baked_count=0
for value in "${baked_values[@]}"; do
  if [[ -n "$value" ]]; then
    baked_count=$((baked_count + 1))
  fi
done

if [[ "$baked_count" -ne 0 && "$baked_count" -ne 3 ]]; then
  echo "[ci] Incomplete baked Pluto metadata in image environment" >&2
  exit 1
fi

if [[ "$baked_count" -eq 3 ]]; then
  require_match "POLCERT_PLUTO_IMAGE" "$PLUTO_IMAGE" "${POLCERT_PLUTO_IMAGE}"
  require_match "POLCERT_PLUTO_GIT_REMOTE" "$PLUTO_GIT_REMOTE" "${POLCERT_PLUTO_GIT_REMOTE}"
  require_match "POLCERT_PLUTO_GIT_COMMIT" "$PLUTO_GIT_COMMIT" "${POLCERT_PLUTO_GIT_COMMIT}"
else
  echo "[ci] No baked Pluto metadata found; validating live /pluto checkout only"
fi

for value in "${buggy_baked_values[@]}"; do
  if [[ -z "$value" ]]; then
    echo "[ci] Incomplete baked buggy-Pluto metadata in image environment" >&2
    exit 1
  fi
done
require_match "POLCERT_BUGGY_PLUTO_GIT_REMOTE" "$PLUTO_BUGGY_GIT_REMOTE" "${POLCERT_BUGGY_PLUTO_GIT_REMOTE}"
require_match "POLCERT_BUGGY_PLUTO_GIT_COMMIT" "$PLUTO_BUGGY_GIT_COMMIT" "${POLCERT_BUGGY_PLUTO_GIT_COMMIT}"
require_match "POLCERT_BUGGY_PLUTO" "$PLUTO_BUGGY_ROOT/tool/pluto" "${POLCERT_BUGGY_PLUTO}"
require_match "POLCERT_BUGGY_POLYCC" "$PLUTO_BUGGY_ROOT/polycc" "${POLCERT_BUGGY_POLYCC}"

actual_remote="$(git -C /pluto remote get-url origin)"
require_match "/pluto origin" "$PLUTO_GIT_REMOTE" "$actual_remote"

actual_head="$(git -C /pluto rev-parse HEAD)"
if [[ "$actual_head" == "$PLUTO_GIT_COMMIT" ]]; then
  :
elif git -C /pluto merge-base --is-ancestor "$PLUTO_GIT_COMMIT" "$actual_head" &&
     git -C /pluto diff --quiet "$PLUTO_GIT_COMMIT..$actual_head" -- . ':(exclude)Dockerfile'; then
  echo "[ci] Pluto checkout includes packaging-only commits on top of the pinned compiler baseline" >&2
else
  echo "[ci] Pluto baseline mismatch for /pluto HEAD" >&2
  echo "[ci]   expected compiler baseline: $PLUTO_GIT_COMMIT" >&2
  echo "[ci]   actual HEAD:              $actual_head" >&2
  exit 1
fi

if ! git -C /pluto diff --quiet --ignore-submodules=dirty HEAD -- . ':(exclude)Dockerfile'; then
  echo "[ci] Pluto tracked compiler sources differ from the pinned baseline" >&2
  git -C /pluto status --short --branch >&2
  exit 1
fi

buggy_remote="$(git -C "$PLUTO_BUGGY_ROOT" remote get-url origin)"
require_match "$PLUTO_BUGGY_ROOT origin" "$PLUTO_BUGGY_GIT_REMOTE" "$buggy_remote"

buggy_head="$(git -C "$PLUTO_BUGGY_ROOT" rev-parse HEAD)"
require_match "$PLUTO_BUGGY_ROOT HEAD" "$PLUTO_BUGGY_GIT_COMMIT" "$buggy_head"
if ! git -C "$PLUTO_BUGGY_ROOT" diff --quiet --ignore-submodules=dirty HEAD -- . ':(exclude)Dockerfile'; then
  echo "[ci] Bug-reproduction Pluto sources differ from the pinned baseline" >&2
  git -C "$PLUTO_BUGGY_ROOT" status --short --branch >&2
  exit 1
fi

short_commit="${PLUTO_GIT_COMMIT:0:7}"
buggy_short_commit="${PLUTO_BUGGY_GIT_COMMIT:0:7}"

require_binary_version() {
  local binary="$1"
  local expected_short_commit="$2"
  local version_line
  version_line="$("$binary" --version 2>&1 | sed -n '1p' || true)"
  if [[ "$version_line" != *"$expected_short_commit"* ]]; then
    echo "[ci] Pluto binary $binary does not mention pinned commit $expected_short_commit" >&2
    echo "[ci]   $binary --version: $version_line" >&2
    exit 1
  fi
}

require_binary_version pluto "$short_commit"
require_binary_version /pluto/tool/pluto "$short_commit"
require_binary_version "$POLCERT_BUGGY_PLUTO" "$buggy_short_commit"

require_glpk_family_flags() {
  local binary="$1"
  local help_text
  help_text="$("$binary" --help 2>&1 || true)"
  for required_flag in "--glpk" "--lp" "--dfp"; do
    if [[ "$help_text" != *"$required_flag"* ]]; then
      echo "[ci] Pluto binary $binary does not advertise required GLPK-family flag $required_flag" >&2
      exit 1
    fi
  done
}

require_glpk_family_flags pluto
require_glpk_family_flags /pluto/tool/pluto
require_glpk_family_flags "$POLCERT_BUGGY_PLUTO"

echo "[ci] Pluto baselines OK: fixed=$short_commit buggy=$buggy_short_commit remote=$PLUTO_GIT_REMOTE"
