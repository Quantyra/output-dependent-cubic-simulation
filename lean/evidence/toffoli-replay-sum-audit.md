# Three-wire Toffoli replay of an arbitrary represented state

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ToffoliSuperposition.lean` SHA-256 `7fa8618d73c2f316e68787d5ede556bae69491e371fb63d75ff16726a1bed307`.

The locked Lean 4.30.0 project build passed (82 jobs). `sharedAddSame_exponent` uses no axioms; `weightedBasis_exponent` uses `[propext, Quot.sound]`; the other four declarations use `[propext, Classical.choice, Quot.sound]`. By combining the eight-basis decomposition, coefficient scaling, denominator shifts and replay addition, the literal Toffoli record list is shown to succeed for every represented three-wire state and produce the sum of the eight weighted basis replay results. The chosen basis results are noncomputable proof witnesses; the interpreter itself remains executable.

The theorem does not yet equate that sum with the ideal Toffoli action. Arbitrary wires, complex embedding, Python correspondence, full circuit behavior, costs and all labeled manuscript theorems remain open.
