# Successful pivot programs solve every target

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/PivotSolveCorrect.lean` SHA-256 `603692517272259bfd6635b99d6f75f8ea72e0f589f049775edaf4a516b7ff06`.

Lean 4.30.0 with locked dependencies: `lake build` passed (37 jobs), and the 95-declaration axiom audit passed. The actual matrix evaluator maps the identity matrix to its input. Whenever the actual pivot generator returns a program, execution on any target yields a solution to the original equation, and the checked solver returns that solution. The main declarations depend on `[propext, Classical.choice, Quot.sound]`.

Generator success on every invertible input is still unproved. Finite-encoding runtime, native circuit semantics and all labeled manuscript theorem certifications remain open.
