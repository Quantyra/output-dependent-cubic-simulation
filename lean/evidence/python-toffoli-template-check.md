# Python and Lean Toffoli template comparison

The static checker `tools/check_toffoli_template.py` passed against `src/check_acceptance_estimator.py` SHA-256 `711b7b8f635f123e915ed145d07e2010cc29a571ae9cdfd90237a5b70a08ea1e` and `lean/SectorSimulation/ThreeWireProgram.lean` SHA-256 `3aad6013ac2cd6dcd831c8e2b6fe2036f6b53a783b3f2c6a5909963bef8eb747`. It requires the Python function to be a single literal return list over the three parameters and extracts the Lean typed Toffoli list, comparing all 15 gate tags and ordered parameter roles. The package workflow runs the checker on future changes.

This independently checks source template agreement for arbitrary argument substitution. It is not a Lean proof of Python semantics, an end-to-end compiler equivalence proof, or a certification of any manuscript theorem.
