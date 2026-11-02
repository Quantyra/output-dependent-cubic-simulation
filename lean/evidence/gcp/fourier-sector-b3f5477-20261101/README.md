# GCP certification evidence: the Fourier factor reindexed onto the sector coset

Source/audit commit: `b3f547780dde9cfe23ec0e4a512b33739a0d741e`.

The exact Lean source archive is `fs-b3f5477-source.tar` (SHA-256 `df667084a19ad56b0be53a229e6be5cadd14a63965b024e5639a653f714013e1`, 1,951,232 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-01` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,256 jobs). Integrated `Audit.lean` and the expected-axiom checker passed on all 897 registered declarations, with no `sorryAx`.

## What was proved

`F_J` acting on a sector state sums over the whole character space, but the sector amplitude vanishes off its coset, so the sum is really a sum over the coordinate space. This module makes that reindexing precise. New module `SectorSimulation/WalshSectorFourierSector.lean`:

- `dropFirst` and four structural lemmas (`mem_dropFirst_subset`, `mem_dropFirst_of_ne`, `not_mem_dropFirst_self`, `nodup_dropFirst`): a removal operation on vector lists, defined locally because the core `List.erase` requires a `BEq` instance that the function type `Fin n → Bool` does not have.
- `foldr_dropFirst`: a list sum splits at any element that occurs in it.
- `foldr_zero_of_all`: a list sum all of whose terms vanish is zero.
- `foldr_reindex_of_injective`: the general sum-over-the-image step — for an injective map, a nodup index list, a nodup character list containing the whole image and a summand vanishing off the image, the two `List.foldr` sums agree. This is the step that had to be built by hand because `ExactAmplitude` carries no additive monoid instance, so no `Finset.sum` is available and every sum in the development is a `List.foldr` over `binaryBasis`.
- `characterFourier_sectorAmplitude`: the sector instance — the character-space Fourier fold equals the coordinate-space coset fold, with the paper normalization factored out and the sum **left unevaluated**.

## Scope, stated first because the receipt is easy to overread

This **names the object** the matched-sector identity must evaluate; it evaluates nothing. The sum produced here still contains the phase of `f0`, so:

- no Gauss-sum value and no `2^(r/2)` scaling is obtained — that comes from evaluating the sum, not from reindexing it;
- nothing shows the result is supported on the neighbouring coset `a + eta`;
- no phase `theta_a`, no `F_J F_J`, no unitarity, no `Z_e`, no `eta`, no observable, no matched vector, no overlap clause and no paper literal `D` is produced;
- the sector state is still not identified with the manuscript's `psi_a`.

The normalization factor is written `iterateHadamardScale n exactOne`, not a dyadic: `2^(-n/2)` is not an element of the exact amplitude quotient for odd `n`, and both reviews required that this not be papered over.

## Review record

The statement was frozen and reviewed twice before any code. Both returned APPROVE WITH CHANGES and required the same three things, all applied: name the factor as `iterateHadamardScale` rather than a non-existent dyadic; label the result as naming the sum rather than computing it; and record the quotient-versus-complex route decision (operator algebra in the quotient, modulus and order statements in `ℂ`).

The two reviews disagreed on the next increment and the disagreement is recorded rather than resolved by fiat: one holds that the coset Gauss sum is the recorded first unsupported implication and should come next; the other holds that the sum is not generically a quadratic Gauss sum because it contains `f0`, and that `F_J F_J` plus `Z_e` should come first, with the quadratic evaluation brought in only at the matched-sector kernel.

Five compile attempts were needed, all presentational: the core `List.erase` requiring a missing `BEq` instance, a mis-parenthesized foldr expression, an induction hypothesis argument order, and two membership/rewriting slips. No statement changed.

All seven published theorem labels remain `planned`; no published theorem is certified.
