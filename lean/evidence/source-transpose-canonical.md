# Source Walsh sum with constructed transformed character

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/SourceTransposeCanonical.lean` SHA-256 `d8eacea911dc1a016c89ed6eb42894bfd6077bdb28d871e93efa5e1b97df2e4b`.

Lean 4.30.0 checked the declaration in a combined source probe; it reports `propext`, `Classical.choice`, and `Quot.sound`. For an arbitrary source ANF and binary character, if the modeled Gaussian program succeeds and the source phase under that coordinate change equals the supplied canonical ANF, the theorem evaluates the source Walsh sum with the transformed character constructed by applying the matrix transpose. No separate pointwise character identity is assumed.

The canonical phase equality and successful coordinate program remain explicit hypotheses. Constructing canonical coordinates for arbitrary source quadratics, general rank/support and elimination costs, and all labeled manuscript theorems remain open.
