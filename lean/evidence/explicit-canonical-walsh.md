# Explicit canonical Walsh enumeration

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExplicitCanonicalWalsh.lean` SHA-256 `c56213f4de75fbce6c4b357d0144eaf185416258d40827147c4d52eaddbf026d`.

Lean 4.30.0 checked the three declarations locally. The pair enumeration theorem depends on `propext`; the two canonical enumeration theorems depend on `propext` and `Quot.sound`. Explicit generated Boolean pair and radical assignments are evaluated under their canonical quadratic and linear phase terms, with any constant bit. Their signed integer sum equals the earlier recursive sum and its closed value, including empty cases.

This connects the canonical-coordinate formula to an explicit assignment enumeration. A connection to the manuscript's finite-vector/ANF grammar, proof that arbitrary quadratic inputs admit a computed canonical basis, polar rank, affine support and elimination cost remains open. No labeled paper theorem is certified.
