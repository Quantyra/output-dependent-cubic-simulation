# Clearing a complete pivot column

Target bridge: section 2 of https://doi.org/10.5281/zenodo.23754698. Source `lean/SectorSimulation/ClearColumnComplete.lean` SHA-256 `0cc45aaf614f8f65b1668140ef20ad4ddf9bf8ed970b2151514fd9f9d42ed386`.

Lean 4.30.0 with locked dependencies: `lake build` passed (34 jobs), and the 79-declaration axiom audit passed. With a set diagonal pivot, the actual generated clearing program sets every distinct row's pivot-column entry to false, including entries initially false. The proof uses a no-duplicates row-list induction and the previously verified pivot-row preservation. The main theorem depends on `[propext, Classical.choice, Quot.sound]`; its induction helper uses `[propext, Quot.sound]`.

This completes the single-column clearing fact, not preservation of earlier columns through later pivots, elimination completeness, runtime, native circuit semantics or any labeled manuscript theorem.
