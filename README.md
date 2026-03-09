# PolCert: Verified Validation for Affine Polyhedral Scheduling

This repository contains mechanized proof of "Verified Validation for Affine Polyhedral Scheduling" in the Coq proof assistent. It contains a general verified validation framework (PolCert), and its verified instantiation of a [CompCert](https://github.com/AbsInt/CompCert) instruction's variant (CInstr). The algorithm's completeness is evaluated with [the Pluto compiler](https://github.com/bondhugula/pluto).


<details><summary>(click to expand) <strong>The paper of this mechanization is published at <a href='https://link.springer.com/chapter/10.1007/978-3-031-64626-3_17'>springer</a>. If you find this project useful, please consider cite us! :D </strong></summary>


```
@InProceedings{10.1007/978-3-031-64626-3_17,
author="Li, Xuyang
and Liang, Hongjin
and Feng, Xinyu",
editor="Chin, Wei-Ngan
and Xu, Zhiwu",
title="Verified Validation for Affine Scheduling in Polyhedral Compilation",
booktitle="Theoretical Aspects of Software Engineering",
year="2024",
publisher="Springer Nature Switzerland",
address="Cham",
pages="287--305",
abstract="Structural nested loops can be abstracted into polyhedral models, based on which one can perform aggressive loop optimizations; however, the optimizations are often heuristic and complex, and therefore error-prone. Meanwhile, verified compilers, though rigorously correct, still miss powerful optimizing transformations and therefore produce less efficient code than industrial ones. To bridge this gap, this work provides a general verified validation framework based on Bernstein's conditions for affine scheduling, the core component of polyhedral optimization techniques. It is parameterized over the concrete definitions and proofs of the instruction language to be reusable. As shown in our evaluation, the framework is flexible enough to support both existing verified compilers like CompCert and existing polyhedral compilers like Pluto. The result is fully mechanized in the Coq proof assistant.",
isbn="978-3-031-64626-3"
}
```


</details>


**Acknowledgement**: This project bases on [Verified Polyhedra Library (VPL)](https://github.com/VERIMAG-Polyhedra/VPL) and [PolyGen](https://github.com/Ekdohibs/PolyGen), and similar idea can be found at [s2sloop](https://github.com/pilki/s2sLoop).

## Overview

PolCert now exposes two user-facing tools:

1. `polcert`: the original validator-only executable. It reads two polyhedral models in [OpenScop format](https://github.com/periscop/openscop), converts them to the internal polyhedral representation with `from_openscop_complete`, and checks refinement/equivalence with the verified validator. This path is unchanged in purpose: it validates scheduler output, but does not run extraction or code generation.
2. `polopt`: a loop-language frontend plus the verified optimization core. It parses a restricted structured loop fragment, extracts a polyhedral model, validates an external Pluto schedule, converts the scheduled polyhedron back to internal form, runs verified code generation, and finally runs verified cleanup passes on the generated loop.

The validator takes two polyhedral models (before and after auto-transformation like Pluto's core algorithm) and outputs their equivalence/refinement status. It only handles models with strictly equal instructions that differ by schedule (scattering) functions, so it validates affine instance reordering rather than more structural transforms such as tiling. The validation algorithm constructs dependence-checking polyhedra for all WAW/WAR/RAW pairs.

Users instantiate their own [Instr](./polygen/InstrTy.v), which requires proving that the instruction semantics imply permutability under [Bernstein’s Conditions](https://link.springer.com/referenceworkentry/10.1007/978-0-387-09766-4_521), together with a verified checker for read/write access functions. We provide CompCert's instruction language ([CInstr](./src/CInstr.v)) as the main instantiation and a lighter syntax-oriented instruction language ([SInstr](./syntax/SInstr.v)) for the `polopt` frontend.

The verified optimization core now lives in [driver/PolOpt.v](./driver/PolOpt.v). The final `Opt` definition is the prepared pipeline (`Opt_prepared`), and the main theorem is `Opt_correct`. The proved passes in that pipeline are:

- `Extractor.extractor`: verified `Loop -> PolyLang` extraction ([src/Extractor.v](./src/Extractor.v))
- `StrengthenDomain.strengthen_pprog`: conservative statement-domain strengthening by implied parameter guards ([src/StrengthenDomain.v](./src/StrengthenDomain.v))
- `scheduler'`: external scheduler wrapped by verified validation ([driver/PolOpt.v](./driver/PolOpt.v))
- `PrepareCodegen.prepare_codegen`: reconciles explicit-depth polyhedral semantics with the codegen-ready representation ([src/PrepareCodegen.v](./src/PrepareCodegen.v))
- `CodeGen.codegen`: verified polyhedral code generation ([polygen/CodeGen.v](./polygen/CodeGen.v))
- verified post-codegen cleanup passes:
  - affine expression/test simplification ([polygen/LoopCleanup.v](./polygen/LoopCleanup.v))
  - structural `Seq` / trivial `Guard` cleanup ([polygen/LoopCleanup.v](./polygen/LoopCleanup.v))
  - singleton-loop elimination by substitution ([polygen/LoopSingletonCleanup.v](./polygen/LoopSingletonCleanup.v))

What is *not* covered by the Coq correctness theorem: the textual `.loop` parser/elaborator, OpenScop I/O implementation details, Pluto itself, and the final pretty-printer. Those are engineering layers around the verified core.

Current regression status:

- `polcert` remains the original validator tool and is intentionally unaffected by the `polopt` work.
- strict proved-path `polopt` runs the full generated benchmark suite (`62/62` cases succeed).
- among these, `52` cases exhibit a real optimization/change in the emitted loop, and `10` are unchanged.

## Structure

Main proofs can be found in [`./src`](./src) folder. Unit tests are in [`./tests`](./tests) folder; [`./tests/pluto-all`](./tests/pluto-all) includes all 62 test cases evaluated with Pluto. 

For more complete project information, see [documentation](#documentation).

<details><summary>(click to expand) <strong>Project structure</strong></summary>


```
.
├── Dockerfile, Makefile[...], configure
├── README.md
├── doc                # Chore: for documentation 
├── src                # Coq: main machanization of this project
├── VPL                # Coq: Verified Polyhedra Library
├── polygen            # Coq: PolyGen's machanization
├── flocq              # Coq: Floating point Library, used by CompCert
├── cfrontend, common, lib, x86, x86_64  # Coq: (mainly) CompCert Coq files
├── tests              # Chore: test suit and test scripts
├── cparser, driver    # OCaml: compiler driver, amended from CompCert's
├── extraction         # Chore: for coq file's ocaml extraction 
├── samples            # Coq: sample polyhedral programs (instantiate with CInstr) 
├── tools              # Chore: just some tools
└── MenhirLib          # TBD: the verified parser, may reuse it later, now useless
```


</details>


## Usage

### Build (Docker)

We recommand you to test our implementation with docker. You can build the docker image from scatch with (see [Dockerfile](./Dockerfile)):

```
# this may take (less-than) 30 minutes, depend on your network condition
docker build . -t polcert
```

You can also fetch the offical image (may not be updated in time, but it should work) from [the provided docker-hub repository](https://hub.docker.com/repository/docker/hughshine/polcert/) by:

```
docker pull hughshine/polcert:latest
```

Then you can run the project inside the docker:

```
sudo docker run -p 80:80 -ti [--rm] [hughshine/]polcert:latest
```

Inside the docker container, the recommended build order is:

```
make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
make test
```

The extracted executables are:

- `polcert <before.scop> <after.scop>`: validator-only CLI
- `polopt <file.loop>`: loop-frontend optimizer CLI

For the generated loop benchmark suite used by `polopt`, see [tests/polopt-generated/README.md](./tests/polopt-generated/README.md).

You can run `make check-admitted` for unfinished proofs. No additional axioms are introduced (you have to manually check this). You can count lines of code of Coq with [cloc](https://github.com/AlDanial/cloc) with `make loc` (note that the satistics is not complete, but roughly accurate; we added some code to library files).

For the docker image, it bases on [prebuild pluto base image](https://hub.docker.com/repository/docker/hughshine/pluto-verif) (we modify pluto to dump its intermediate representation), installs coq/ocaml environment (and some tools), and prepares the configuration. See the [Dockerfile](./Dockerfile) for more details. If you want to install the project manually, just follow the steps in [Dockerfile](./Dockerfile).

### Documentation

You can generate project's full documentation by `make documentation` (After running `make`) and view it at [localhost](http://localhost/) (If you use the docker image).

### Try your own test case

If your build and installation succeeds, there should be executable `polcert` in your PATH. `pluto` (see [here](https://github.com/verif-scop/pluto)) is already in your path. The `polcert` usage below is unchanged and remains the reference way to validate two OpenScop models.

For the optimizer entrypoint, `polopt` accepts the structured `.loop` syntax described in [syntax/README.md](./syntax/README.md).

Now you can write your own validator test case (`vim` is provided in the image) like `test.c`,

```
#pragma scop
// Your loop should be surrounded with pragma
// You don't need to write complete c program, as pluto intercepts the fragment
#pragma endscop
```

and then invoke `pluto` with 

```
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
      --smartfuse --nounrolljam --noparallel --notile --rar test.c
```

If compilation succeeds, intermediate files (see [OpenScop format](https://github.com/periscop/openscop)) are generated:

```
ls *.scop
# test.afterscheduling.scop
# test.beforescheduling.scop
```

The run `polcert <pol1> <pol2>` on them. Note that `polcert` tries to run the validation algorithm twice, so any order is ok.

```
polcert test.beforescheduling.scop test.afterscheduling.scop
```

It will give output like:

```
[EQ] The two polyhedral models (test.beforescheduling.scop, test.afterscheduling.scop) are equivalent.
# or
[GT] Polyhedral model test.beforescheduling.scop refines test.afterscheduling.scop.
# or
[LT] Polyhedral model test.afterscheduling.scop refines test.beforescheduling.scop.
# or
[NE] Cannot determine refinement relations between the two polyhedral models (test.afterscheduling.scop, test.beforescheduling.scop).
```

--- 

## Note: Warning Suppression

We turn off several warnings for clarity. Three additional (and unimportant) Coq warnings were turned off comparing to CompCert. OCaml's warnings are not discussed as they do not affect formal guarantees (most of them come from extracted VPL code).

**Coq compilation (see [Makefile](./Makefile)):**
1. `-unused-pattern-matching-variable`: disabled in CompCert
2. `-deprecated-ident-entry`: disabled in CompCert
3. `-implicit-core-hint-db`: inherit from PolyGen, to be solved upsteam
4. `-deprecated-hint-without-locality`: inherit from PolyGen, to be solved upsteam
5. `-undeclared-scope`: library file, to be solved

**Coq extraction (see [extraction.v](./extraction/extraction.v)):**
1. `-extraction-ambiguous-name`, does not matter
2. `-extraction-opaque-accessed`, to be fixed in VPL

**Ocaml compilation (see [Makefile.extr](./Makefile.extr)).**


## LICENSE

See [LICENSE](./LICENSE). We follow [PolyGen](https://github.com/Ekdohibs/PolyGen).
