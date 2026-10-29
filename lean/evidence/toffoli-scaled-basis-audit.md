# Scaled Toffoli basis amplitude

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ToffoliScaledBasis.lean` SHA-256 `9a5d36c01207df83225204ff879e15a101935b027ee27c70a07fe7aa9bdf56fc`.

The locked Lean 4.30.0 build passed (79 jobs); both declarations use `[propext, Classical.choice, Quot.sound]`. The amplitude of a scaled and denominator-shifted state equals the quotient product of the corresponding dyadic coefficient and the original amplitude. Using this identity and the checked literal Toffoli basis replay, every output amplitude equals the ideal result for every three-bit basis input with any cyclotomic coefficient and natural denominator shift.

This does not establish correctness on arbitrary superpositions or arbitrary wires. Complex embedding, Python correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
