# Toffoli decomposition Boolean phase polynomial

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ToffoliPhasePolynomial.lean` SHA-256 `01345a1dafad41aeac5a31c30b2f21d15f2fd64d156c115fbb8c281856dfa0d6`. The modeled XOR and T/TDG exponent expressions correspond to the wire sequence in `src/check_acceptance_estimator.py:254`.

Lean 4.30.0 locked project build passed (59 jobs). The three declarations have no axiom dependencies. The modeled target and control XOR networks restore their bits, and the modeled phase exponent equals four times the cubic Boolean monomial modulo eight. The finite Boolean cases are discharged by kernel reduction, not native evaluation.

The connection of these expressions to literal native-record execution, complex eighth-root amplitudes, normalized Hadamards, Python equivalence, full circuit behavior, cost and all labeled manuscript theorems remains open.
