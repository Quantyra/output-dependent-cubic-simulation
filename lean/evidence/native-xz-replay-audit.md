# Native X, Z and CNOT record replay

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/NativeXZReplay.lean` SHA-256 `50569680f74a2d1341b1b893815e26c86665b203e730ebb9b39012f59b2ff992`.

Lean 4.30.0 locked project build passed (56 jobs). Exact audited axiom sets appear in `CLAIMS.json`, within the permitted baseline. Literal X Z X Z records replay as global negation; a literal Z record yields the single-wire phase; a valid literal CX record yields the modeled CNOT amplitude action. The executable replay rejects unsupported records and invalid wire indices.

No correspondence to Python execution or proof of Hadamard, multiwire phase, normalization, full circuit, cost or any labeled manuscript theorem is claimed.
