# Canonical character Walsh sum

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/CanonicalCharacterSum.lean` SHA-256 `84dc2e58d4946a1f510b9cc6508e3d95fdfc54da93fc0fb9676300ffc34e6229`.

Lean 4.30.0 checked both recorded declarations in a combined source probe; each reports `propext`, `Classical.choice`, and `Quot.sound`. Given canonical pair and radical phase coefficients and explicit linear character coefficient lists of the stated dimensions, XORing the character into the phase shifts its coefficients by XOR. Summing over all finite canonical vectors yields zero if a shifted radical coefficient is nonzero, and otherwise the exact signed power of two with shifted pair signature. Zero dimensions and constant bits are included.

The explicit character still needs to be connected to the standard finite-vector dot product; this does not construct canonical coordinates for arbitrary source quadratics or prove general affine support, polar rank, elimination costs or the full paper Walsh lemma. No labeled manuscript theorem is certified.
