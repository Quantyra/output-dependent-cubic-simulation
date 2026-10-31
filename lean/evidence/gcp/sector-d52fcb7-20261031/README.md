# GCP certification evidence: affine residual support equation

Source/audit commit: `d52fcb7789b3870331f7a53ceb25e9246472e11c`.

The exact Lean source archive is `sector-d52fcb7-source.tar` (SHA-256 `074de6fd672fae28461c2e6a690afd7786593db7dab9ebc047ceaadb9191bdce`, 1,423,360 bytes). It contains tracked Lean sources and the exact axiom checker, excluding previous evidence archives; the checksum was verified on the builder before compilation.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-02` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,175 jobs). The integrated `Audit.lean` and exact expected-axiom checker both passed.

The new source theorem states that nonzero Walsh support is exactly the fiber where the linear residual-character component equals its fixed offset. It follows from the proved decomposition of the generated residual vector into that linear component XOR the offset. New theorem axiom dependencies are within the existing baseline: the decomposition, XOR-zero equivalence, and zero-fiber equivalence use `propext` and `Quot.sound`; the source-specific support theorem also uses `Classical.choice`.

This identifies support as a generated-coordinate affine fiber, but does not prove that its kernel equals `im(Bq)`, establish the polar rank or support nonemptiness, normalize the Walsh values, establish matched-sector bounds or costs, or certify a labeled paper theorem.
