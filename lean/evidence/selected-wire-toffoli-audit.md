# Selected-wire typed Toffoli correctness

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ThreeWireProgram.lean` SHA-256 `3aad6013ac2cd6dcd831c8e2b6fe2036f6b53a783b3f2c6a5909963bef8eb747`.

The locked Lean 4.30.0 build passed (86 jobs). The native three-wire correspondence, embedding recovery and ideal Toffoli slice declarations use `[propext, Quot.sound]`; the other four declarations use `[propext, Classical.choice, Quot.sound]`. Arbitrary finite typed gate programs commute with selected-wire slicing. The typed Toffoli sequence corresponds to the literal native records on three wires, and for any injective selection of three wires in an arbitrary represented state, its exact output amplitude equals that of modeled ideal Toffoli at every output vector.

The theorem is about typed selected-wire execution; correspondence with native-record replay in larger dimensions and Python compiler records remains open. Complex embedding, full circuit behavior, costs and all labeled manuscript theorems also remain open.
