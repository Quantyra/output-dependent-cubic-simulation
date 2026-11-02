# GCP certification evidence: character-space sector norm and the diagonal phase factor

Source/audit commit: `a95804c076e67bc231431efdb6e76f6143737c8d`.

The exact Lean source archive is `obs-a95804c-source.tar` (SHA-256 `a4a570bd70964cc46a0fbab1a0c04ccc47d943f3391bf78e8c7badc32ce6ae96`, 1,914,880 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-01` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,254 jobs). Integrated `Audit.lean` and the expected-axiom checker passed on all 881 registered declarations, with no `sorryAx`.

## Scope of the receipt, stated first

This is **not** the observable and not its action on the sector state. The manuscript's `O = F_J D_f1 F_J Z_e F_J D_f1 F_J` and the matched-sector identity `O_a psi_a = e^(i theta_a) psi_(a+eta)` at the paper `2^(-n/2)` normalization are untouched: they need the Gauss-sum evaluation, which the lane records as the first unsupported implication of the layer.

What is proved is the two pieces that must exist before the observable can even be written down.

## What was proved

New module `SectorSimulation/WalshSectorObservable.lean`:

- `sectorAmplitude_sum_normSq`: the unit-norm sum transports from the coordinate index to the character space, using that the extension vanishes off the coset and that the point map is injective at a fixed label. This is the genuine content of the increment: `F_J` can only act on the ambient character space, so the `y`-indexed vector is the wrong object for the observable.
- `sectorAmplitude_unit_norm`: the character-space sector vector is a unit vector.
- `sectorDiag`: `D_f1`, the character-basis diagonal phase acting on a character-space vector.
- `sectorDiag_support`, `sectorDiag_eq_zero_of_not_support`: the diagonal factor cannot move a sector's support.
- `sectorDiag_normSq`, `sectorDiag_unit_norm`, `sectorDiag_disjoint`: it preserves every squared modulus, hence the unit norm and the disjointness across labels.
- Supporting declarations: `sectorSupportPoint_injective_at_label`, `normSq_complexSigned` (the general signed modulus; the earlier lemma covered only the value at one), `exactSigned_zero`.

The statement was frozen and reviewed twice before any code. Both reviews required the same narrowing, and it is applied: the character-space norm is the content; `sectorDiag` is scaffolding; and the norm and support preservation are recorded as helper facts, because they hold for *any* unimodular phase and therefore say nothing about `f1`. The reviews also supplied `sectorSupportPoint_injective_at_label` and `normSq_complexSigned` as missing prerequisites, and both are here.

Two compile failures occurred and both were presentation: an unreduced beta-redex after `set`, and `Finset.sum_subset` being applied in the wrong direction. The audit checker then failed on unquoted set literals in its new expectation rows, which cost one corrected re-run of the exact-source chain.

Explicitly **not** proved, and the receipt must not be read otherwise: no Fourier factor, no `Z_e`, no `eta = C l0`, no `2^(-n/2)` normalization, no matched-sector identity, no `|X_a| <= 1`, no symmetry `X_a = X_(a+eta)`, no sector average, and no identification with the manuscript's objects. `prop:sector` remains `planned` and no published theorem is certified.
