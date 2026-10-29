# Source Walsh sum under known canonical coordinates

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/SourceCanonicalCharacter.lean` SHA-256 `09075c283f18558e04b990af38873fc954176684d42973046fa623002acf2084`.

Lean 4.30.0 checked the declaration in a combined source probe; it reports `propext`, `Classical.choice`, and `Quot.sound`. Given a source ANF, an arbitrary binary character and a matrix with a successful modeled Gaussian row program, if the source phase after that coordinate change is pointwise the supplied canonical ANF and its transformed character is pointwise the supplied binary character, the source Walsh sum equals the explicit canonical zero-or-signed-power-of-two expression.

Both pointwise identities are hypotheses, not a general canonicalization algorithm or a constructed transpose. General affine support, polar rank, sign representation, costs and all labeled manuscript theorems remain open.
