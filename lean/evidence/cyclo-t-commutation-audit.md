# Exact modeled T and TDG commutation

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CycloTCommutation.lean` SHA-256 `c1b55344ee4d449e93942d4d02a580cb090c14fd5e17d23e9af3ce553df16340`.

Lean 4.30.0 locked project build passed (64 jobs). Exact axiom sets are in `CLAIMS.json` and remain within the permitted baseline. The represented T and TDG diagonal multipliers commute with a disjoint Hadamard numerator, including when that numerator is scaled by the represented square root of two. The latter is twice the intended normalized Hadamard scale, pending division by two.

No complex embedding, division by two, physical normalized gate semantics, literal Toffoli replay, Python equivalence, cost or labeled manuscript theorem is proved here.
