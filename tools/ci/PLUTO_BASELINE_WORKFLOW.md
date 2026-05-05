# Pluto Baseline Workflow

This repository now treats the Pluto baseline as explicit CI input rather than
an implicit property of `hughshine/pluto-verif:latest`.

## Source of truth

`tools/ci/pluto-baseline.env` is the single source of truth for:

- `PLUTO_IMAGE`: the Pluto base image currently consumed by PolCert CI
- `PLUTO_BASELINE_TAG`: the versioned Git/image tag name to use when publishing
  the next pinned Pluto baseline
- `PLUTO_VERSIONED_IMAGE`: the versioned Pluto base image name that should
  eventually replace `PLUTO_IMAGE`
- `PLUTO_GIT_REMOTE`
- `PLUTO_GIT_COMMIT`

The PolCert Dockerfile defaults must stay aligned with this file.

`PLUTO_GIT_COMMIT` identifies the pinned Pluto compiler-source baseline.
The published Pluto image/tag may sit on top of that commit with a packaging-only
Dockerfile commit, but it must not change tracked compiler sources.
The PolCert Dockerfile may also rebase `/pluto` to this commit and rebuild it
with GLPK support before building PolCert. That rebuild is part of the pinned
baseline: `--glpk`, `--lp`, and `--dfp` must be available in the live Pluto
binary used by the compatibility suite.

## Current shape

The current flow deliberately preserves the large Docker cache boundary:

1. PolCert still starts from a Pluto base image.
2. The PolCert Dockerfile checks out the pinned Pluto commit and rebuilds Pluto
   with `--enable-glpk --with-glpk-prefix=/usr`.
3. CI passes the Pluto baseline metadata into the PolCert image build.
4. `tools/ci/check_pluto_baseline.sh` verifies the live `/pluto` checkout and
   binary before the main build/test chain.

This keeps existing cache behavior while making Pluto version and GLPK drift
visible. Once a matching Pluto base image is published, `PLUTO_IMAGE` can point
directly at `PLUTO_VERSIONED_IMAGE` and the rebuild step remains an idempotent
guard.

## Pluto-side packaging rule

The Pluto repository Dockerfile should build the current checkout. It should
not `reset --hard origin/master` during the image build.

That packaging rule is intentionally treated as separate from the Pluto
compiler-source baseline check. The checker allows `/pluto` to be a
Dockerfile-only descendant of `PLUTO_GIT_COMMIT`, but still rejects
compiler-source drift.

## How to publish a new pinned Pluto baseline

1. Make the desired Pluto source commit clean and stable in the Pluto repo.
2. Tag it in `verif-scop/pluto`:
   - Example: `polcert-pluto-glpk-candl-6f43860`
3. Build and publish the Pluto base image from the Pluto checkout:

```sh
docker build \
  --build-arg PLUTO_GIT_REMOTE=https://github.com/verif-scop/pluto.git \
  --build-arg PLUTO_GIT_COMMIT=6f43860b6c4cddeeca09189bf3073f05b78b14a5 \
  -t hughshine/pluto-verif:polcert-pluto-glpk-candl-6f43860 \
  /path/to/pluto
docker push hughshine/pluto-verif:polcert-pluto-glpk-candl-6f43860
```

4. Update `tools/ci/pluto-baseline.env`:
   - set `PLUTO_IMAGE=$PLUTO_VERSIONED_IMAGE`
5. Keep the PolCert Dockerfile defaults aligned with that file.
6. Rebuild and rerun the normal PolCert CI path.

## Validation checklist

After changing Pluto baseline data, rerun:

```sh
bash /polcert/tools/ci/check_pluto_baseline.sh
bash /polcert/tools/ci/run_ci.sh
python3 /polcert/tests/polopt-generated/tools/check_polopt_cases.py \
  --cases-dir /polcert/tests/polopt-generated/cases \
  --expect-total 62 \
  --min-changed 50 \
  --min-nontrivial-changed 50 \
  --require-tiled matmul matmul-init wavefront
```
