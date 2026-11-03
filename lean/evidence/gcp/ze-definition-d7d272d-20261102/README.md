# GCP certification evidence: the Pauli `Z` factor `Z_e`

Source/audit commit: `d7d272dfc51c7fec9c518ddbfde2b16e036925e4`.

The exact Lean source archive is `z-d7d272d-source.tar` (SHA-256 `432790aa5e6bc02f72ad27d3e8d8b29170e5faf14df41a7688032d1cc6ba1cf4`, 1,962,496 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-01` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,257 jobs). Integrated `Audit.lean` and the expected-axiom checker passed on all 901 registered declarations, with no `sorryAx`.

## What this is, and what it is not

This is **one factor of the observable**, not the observable, and it does not move toward the Fourier involution. `characterZ e` is the Pauli `Z` on output wire `e`, diagonal in the computational basis: it multiplies the amplitude at basis label `l` by `(-1)^(l e)`. In `O = F_J D_f1 F_J Z_e F_J D_f1 F_J` the surrounding `F_J` factors carry the basis change, so no Fourier conjugation belongs in this definition. `characterZ_apply` unfolds it; `exactSigned_involutive` and `characterZ_involutive` record that signing twice cancels.

## The reviews cut this increment down

The statement was frozen, then reviewed twice. The recorded next step was "`F_J F_J` and `Z_e`", and both reviews agreed the involution half is **blocked**: it needs the general character orthogonality `sum over l of (-1)^(l·v) = 2^n` for `v = 0` and `0` otherwise, under a symmetric invertible pairing. One review confirmed from the source that no such lemma exists and that no cheaper route is available from `binaryBasis_expansion`, `basisSum_present`/`_absent` or the `hadamardKernel` lemmas; the other corrected the stronger claim that it is wholly absent, noting `canonicalVectorWalshSum_closed` at `k = 0`, `pairs = []`, `radicals = vectorAssignment v`, `c = false` is the orthogonality statement modulo a `vectorAssignment`/dot-parity bridge and a lift to the coefficient system used here. That correction is recorded rather than glossed over.

Both reviews then **removed** items from the frozen increment:

| Dropped | Reason |
| --- | --- |
| `F_J` on a delta has unit norm | a one-line consequence of `characterFourier_delta_complex`, summing `2^n` copies of `2^(-n)`; it does not advance unitarity, which needs orthogonality of *distinct* delta images |
| `Z_e` maps zero to zero | literally the already-proved `exactSigned_zero` |
| arbitrary `BinaryVector n` as the wire index | corrected to `e : Fin n`, matching the paper's one-hot output; the wider signature would smuggle in a dot product the paper pins to a unit vector |

The involution `characterZ_involutive` was kept, but both reviews called it close to vacuous and it is labelled a helper, not a result.

## Honest status

Nothing here is unitarity, `F_J F_J`, the `F_J Z_e F_J` identity, character orthogonality, the coset Gauss sum, the offset `eta`, the observable, the matched vector, any overlap clause, the paper literal `D`, or any correspondence with the manuscript's `psi_a`. `prop:sector` remains `planned` and no published theorem is certified. The inventory already lists `phase-character-orthogonality` as an unproved dependency of `thm:estimator`, so the blocker is a known gap rather than a new finding.
