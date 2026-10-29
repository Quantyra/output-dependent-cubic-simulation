# Exact dyadic coefficient quotient

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/DyadicQuotient.lean` SHA-256 `c5514641bad147bb71957b676ea90646dc96b578a090b671083b7447a430f02b`.

Lean 4.30.0 locked project build passed (69 jobs). All five audited declarations use `[propext, Classical.choice, Quot.sound]`. The module constructs a quotient by the dyadic equivalence and lifts addition, subtraction, multiplication and negation using their compatibility proofs. It checks commutativity of addition and multiplication and proves that twice the squared represented Hadamard scale equals quotient one.

Associativity, distributivity and remaining quotient algebra laws, complex embedding, normalized Hadamard action, literal circuit replay, Python correspondence, cost and all labeled manuscript theorems remain open. The normalization scalar proof uses kernel reduction, not native evaluation.
