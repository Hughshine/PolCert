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
- `PLUTO_BUGGY_GIT_REMOTE`
- `PLUTO_BUGGY_GIT_COMMIT`
- `PLUTO_BUGGY_ROOT`

The PolCert Dockerfile defaults must stay aligned with this file.

`PLUTO_GIT_COMMIT` identifies the pinned Pluto compiler-source baseline.
The published Pluto image/tag may sit on top of that commit with a packaging-only
Dockerfile commit, but it must not change tracked compiler sources.
The PolCert Dockerfile may also rebase `/pluto` to this commit and rebuild it
with GLPK support before building PolCert. That rebuild is part of the pinned
baseline: `--glpk`, `--lp`, and `--dfp` must be available in the live Pluto
binary used by the compatibility suite.

`PLUTO_BUGGY_GIT_COMMIT` identifies a separate historical checkout used only
by the executable miscompilation witnesses. It is never on the ordinary
compiler path. Both revisions are recorded in artifact provenance.

## Current shape

The current flow deliberately preserves the large Docker cache boundary:

1. PolCert still starts from a Pluto base image.
2. An independent Docker builder compiles the historical bug revision while
   the main stage prepares and rebuilds fixed Pluto. BuildKit can run these
   two compiler builds concurrently. The final image exports a clean historical
   checkout plus its runtime binaries, rather than the builder's object files,
   under `/opt/polcert/pluto-buggy`; fixed Pluto remains under `/pluto`.
3. CI passes the Pluto baseline metadata into the PolCert image build.
4. `tools/ci/check_pluto_baseline.sh` verifies both checkout identities,
   source cleanliness, and binaries before the main build/test chain.

This keeps existing cache behavior, avoids serial fixed/buggy compiler builds,
and makes Pluto version and GLPK drift visible. Once a matching Pluto base
image is published, `PLUTO_IMAGE` can point directly at
`PLUTO_VERSIONED_IMAGE`; the rebuild remains an idempotent guard.

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
   - Example: `polcert-pluto-defensive-fixes-8c43c21`
3. Build and publish the Pluto base image from the Pluto checkout:

```sh
docker build \
  --build-arg PLUTO_GIT_REMOTE=https://github.com/verif-scop/pluto.git \
  --build-arg PLUTO_GIT_COMMIT=8c43c210c9c08c5958198f22db4b54000380925e \
  -t hughshine/pluto-verif:polcert-pluto-defensive-fixes-8c43c21 \
  /path/to/pluto
docker push hughshine/pluto-verif:polcert-pluto-defensive-fixes-8c43c21
```

4. Update `tools/ci/pluto-baseline.env`:
   - set `PLUTO_IMAGE=$PLUTO_VERSIONED_IMAGE`
5. Keep the PolCert Dockerfile defaults aligned with that file.
6. Rebuild and rerun the normal PolCert CI path.

The buggy pin changes only when the intended historical reproduction baseline
changes. Do not advance it as part of an ordinary fixed-baseline update.

## Validation checklist

After changing Pluto baseline data, reproduce the remote build and shard
schedule from the repository root:

```sh
docker build --target ci -t polcert-ci:local .
bash tools/ci/run_ci_shards.sh polcert-ci:local
```

The `ci` image target runs `run_ci_build.sh`, including the Pluto baseline
gate and the proof/extraction build. The host-side shard runner then executes
the same isolated test layout as GitHub Actions. `run_ci.sh` remains a slower
sequential in-container equivalence check, not the remote scheduling model.
