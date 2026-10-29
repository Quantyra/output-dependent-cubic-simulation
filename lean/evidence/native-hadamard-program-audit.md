# Native Hadamard programs and linear composition

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ExactHadamardProgram.lean` SHA-256 `4cd56cc235c2a953c07ef0f4655533126b63a4b58a75235e589b1e2af8e716ee`.

The locked Lean 4.30.0 build passed (100 jobs). Native Hadamard replay uses `[propext]`; program concatenation uses no axioms; the other four declarations use `[propext, Classical.choice, Quot.sound]`. Native Hadamard lists replay as their shared-state operations, preserve amplitude equivalence, and cancel when followed by their reverse. All-wire Hadamards followed by the Gaussian native CNOT sequence successfully replay and transport the Hadamard output amplitudes by the source binary matrix.

The all-wire Hadamard action has not yet been identified with the normalized Fourier kernel. Complex embedding, Python correspondence, complete circuit behavior, costs and all labeled manuscript theorems remain open.
