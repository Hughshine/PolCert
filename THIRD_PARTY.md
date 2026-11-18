# Third-party material

Source headers retain the applicable authorship and copyright notices.
PolCert's [LICENSE](LICENSE) does not replace licenses of bundled components.

| Material | Location | License |
| --- | --- | --- |
| CompCert-derived infrastructure | `common/`, `cfrontend/`, `cparser/`, `lib/`, architecture directories | [LICENSE](LICENSE) and file headers |
| Verified Polyhedra Library | `VPL/` | [VPL/LICENSE](VPL/LICENSE) |
| Flocq | `flocq/` | File headers and [LGPL-3.0](licenses/LGPL-3.0.txt) |
| MenhirLib | `MenhirLib/` | File headers and [LGPL-3.0](licenses/LGPL-3.0.txt) |
| PolyGen verified code generator (Courant and Leroy, POPL 2021) | Files with Inria headers in `polygen/` and `lib/` (`Linalg.v`, `VplInterface.v`, `ImpureOperations.v`, `ImpureAlarmConfig.v`, `Heuristics.v`, `Misc.v`, `Mymap.v`, `TopoSort.v`); `src/PolyLang.v` and `polygen/InstrTy.v` derive from it | LGPL-2.1-or-later (file headers) |
| Affine schedule validator (Li, Liang, and Feng, TASE 2024) | `src/AffineValidator.v` (originally `src/Validator.v`) and the instruction and program interfaces in `polygen/InstrTy.v` and `polygen/PolIRs.v`, since extended | [LICENSE](LICENSE) |
| LibTactics (Charguéraud) | `lib/LibTactics.v` | LGPL-3.0 (file header) |
| sflib (Software Foundations Laboratory, SNU) | `lib/sflib.v` | No license notice in the file |
| Pluto-derived benchmark inputs | `tests/`, `evaluation/inputs/` | [Pluto MIT license](licenses/Pluto-MIT.txt) and source notices |

Evaluation manifests record the original loop-corpus path for each kernel.
Content-addressed filenames preserve the experiment input bytes. Supplementary
examples retain any additional attribution in their source comments.
Pluto itself and its dependencies are fetched at pinned commits by the
Dockerfile; their licenses remain in their respective checkouts.
