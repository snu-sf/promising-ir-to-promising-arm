# Putting Weak Memory in Order via a Promising Intermediate Representation

Sung-Hwan Lee, Minki Cho, Roy Margalit, Chung-Kil Hur, Ori Lahav.

Proceedings of the 44th ACM SIGPLAN Conference on Programming Language Design and Implementation ([PLDI 2023](https://pldi23.sigplan.org/)).

This repository contains the coq development of mapping the IR model (PSir) to Armv8S.
The coq development of the source model (vRC11) and the IR model (PSir) can be found [here](https://github.com/snu-sf/promising-ir-coq).
Please visit the [project website](https://sf.snu.ac.kr/promising-ir/) for more information.


## Build

- Requirement: opam (>=2.0.0), Coq 8.15.2
- Installing dependencies with opam
```
./configure
```
- Build the project
```
make -j
```


## Structures

### Armv8S model (Section 5)
- `coq/ir-to-arm/src/axiomatic/Axiomatic.v`: Definition of Armv8S in axiomatic style
- `coq/ir-to-arm/src/promising/Promising.v`: Definition of Armv8S in operational style
- Equivalence betweeen the axiomatic and operational Armv8S models
  - `Theorem axiomatic_to_promising` in `src/axiomatic/AtoP.v`:
  The axiomatic Armv8S refines the operational Armv8S
  - `Theorem promising_to_axiomatic` in `src/axiomatic/PFtoA.v`:
  The operational Armv8S refines the axiomatic Armv8s

### Soundness of mapping PSir to Armv8S (Theorem 5.3)
- `Theorem ps_to_arm` in `coq/ir-to-arm/src/mapping/PStoARM.v`:
Soundness of mapping PSir to Armv8S
