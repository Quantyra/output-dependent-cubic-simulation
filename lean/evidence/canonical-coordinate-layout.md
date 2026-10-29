# Canonical coordinate layout

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalCoordinateLayout.lean` SHA-256 `c5a3c17e0bf5a8e77c7caf30a6800dcc1cacd273919d85b53f0686cc3cfe9f5f`.

Lean 4.30.0 checked all six declarations locally; each reports `propext` and `Quot.sound`. A finite binary vector of dimension `(k+k)+m` splits uniquely into two `k`-coordinate pair blocks and one `m`-coordinate radical block; the join and projections are mutually inverse, including zero-sized blocks.

This is a coordinate-layout bijection only. The generated assignment sums and canonical phase still need to be connected to these blocks and to source ANF; no general quadratic basis, rank, affine support or cost proof follows from it. No labeled paper theorem is certified.
