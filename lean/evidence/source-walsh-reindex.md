# Source Walsh change of coordinates

Target: lemma `lem:walsh` in https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/SourceWalshReindex.lean` SHA-256 `4055d1c7ec29765b5cb3b61bb64e46b53fdb3dd29914384b93551d3de09865e6`.

Lean 4.30.0 kernel checked both declarations locally in a combined source probe; each reports `propext`, `Classical.choice`, and `Quot.sound`. For every source ANF and Walsh character, an invertible matrix accepted by the modeled Gaussian row program reindexes the finite Walsh sum. If, additionally, the transformed source phase XOR the transformed character equals the specified canonical ANF at every vector, its sum has the proved canonical zero-or-signed-power-of-two value.

The canonical phase equality is an explicit hypothesis, not a construction for arbitrary quadratic inputs. This does not prove general affine support, polar rank, sign representation, elimination complexity, Python correspondence, or the full paper Walsh lemma; all labeled paper theorems remain uncertified.
