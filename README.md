# Putting Weak Memory in Order via a Promising Intermediate Representation

The Coq development of the soundness of mapping PSir to Armv8S (Theorem 5.3)

## Structures

### Armv8S model (Section 5)
- `coq/ir-to-arm/src/axiomatic/Axiomatic.v`: Definition of Armv8S in axiomatic style
- `coq/ir-to-arm/src/promising/Promising.v`: Definition of Armv8S in operational style
- `Theorem axiomatic_to_promising` in `src/axiomatic/AtoP.v`:
The axiomatic Armv8S refines the operational Armv8S
- `Theorem promising_to_axiomatic` in `src/axiomatic/PFtoA.v`:
The operational Armv8S refines the axiomatic Armv8s

### Soundness of mapping PSir to Armv8S (Theorem 5.3, in progress)
- `Theorem ps_to_arm` in `coq/ir-to-arm/src/mapping/PStoARM.v`:
Soundness of mapping PSir to Armv8S
