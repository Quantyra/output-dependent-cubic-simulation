# GCP certification evidence: the Fourier factor `F_J` and its replay bridge

Source/audit commit: `3092e769f2ab76f094ef81ab69c26592e2e560aa`.

The exact Lean source archive is `four-3092e76-source.tar` (SHA-256 `749fb1c19559195d6165146bccec2ae9bc75feb383a4be313ead7de148cab1cd`, 1,933,824 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-01` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,255 jobs). Integrated `Audit.lean` and the expected-axiom checker passed on all 888 registered declarations, with no `sorryAx`.

## What was missing and why this is not a duplicate

The development already had the Fourier transform operationally: `nativePythonFourier_normalized_sum` and `nativePythonFourier_paper_kernel` state that the **replayed native program** for the modeled Fourier transformation computes the paper kernel on a `SharedDyadicState`. A `SharedDyadicState` carries one shared exponent and a cyclotomic numerator, so it cannot represent a function that vanishes off a coset — and the sector amplitude is exactly such a function. An operator on arbitrary character-space functions was therefore genuinely absent, and the observable cannot be written down without it.

## What was proved

New module `SectorSimulation/WalshSectorFourier.lean`:

- `characterFourier`: `F_J` on character-space functions, with the paper normalization `(√2/2)^n = 2^(-n/2)` carried by `iterateHadamardScale`, written in the `binaryBasis` foldr convention of the existing replay theorems.
- `characterFourier_replay`: **the bridge.** On a `SharedDyadicState` the operator computes exactly what the replayed native program computes. This is what keeps it from being an unlinked second transform.
- `characterDelta`, `foldr_if_eq_eq`, `characterFourier_basisTerm`: the delta and the collapse of the character sum to its single surviving term.
- `characterFourier_delta`: the action on a basis vector, in the exact quotient.
- `characterFourier_delta_complex`: the paper kernel `2^(-n/2) (-1)^(l·Jc)` as a complex corollary, via the already-proved `realFourierScale_rpow`.

The statement was frozen and reviewed twice before any code. One review **rejected the frozen version** as a floating, unlinked operator and required three things, all applied: add the replay bridge as primary content, match the existing `binaryBasis` foldr summation convention so the bridge is nearly definitional, and reframe the delta action as a definitional check rather than progress. The other review independently required the foldr convention (there is no additive monoid instance on the exact amplitude quotient) and confirmed the normalization design is right for odd `n`.

Two compile attempts were needed and both were presentational in this module — an ill-typed use of the function-valued sum API, replaced by a self-contained collapse lemma — plus one audit-checker re-run because its new expectation rows were written with unquoted set literals.

## Scope, stated first because the increment is easy to overread

This is the operator and its action on a **basis vector**. It is not the observable, and it is not `F_J` applied to a sector state: the coset Gauss sum that the matched-sector identity needs is untouched, and a delta is not a sector amplitude. No Fourier-of-Fourier identity, no unitarity, no `Z_e`, no `eta`, no matched-sector action and no overlap clause is proved. No symmetry or invertibility of `J` is assumed or used. The sector state is still not identified with the manuscript's `psi_a`; all seven published labels remain `planned` and no published theorem is certified.
