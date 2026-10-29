# Three-wire slices of arbitrary states

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ThreeWireSlice.lean` SHA-256 `28953951192ee3e3c08d108be1f5e4f7c4c70959bef9d0120dee6db1093cc6a0`.

The locked Lean 4.30.0 build passed (85 jobs). The first six declarations use `[propext, Quot.sound]`; the CNOT-as-flip and final two CNOT declarations use `[propext, Classical.choice, Quot.sound]`. For any injective selection of three wires, embedding recovers selected bits and commutes with bit flips. Slicing a larger exact state commutes with the modeled H, X, Z, T, inverse T and CNOT operations on the selected wires.

This is a gate-level bridge, not yet a proof of native record replay or arbitrary-wire Toffoli correctness. Complex embedding, Python correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
