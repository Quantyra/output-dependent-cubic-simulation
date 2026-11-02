# GCP certification evidence: sector states are orthogonal by disjoint support

Source/audit commit: `910fac305757ac7af82df49090576bc3e699ac6d`.

The exact Lean source archive is `orth-910fac3-source.tar` (SHA-256 `b4aebf3328232187e55f15aac3ae7aebc5eea491e71857939598288b61e7107b`, 1,891,328 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-01` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,253 jobs). Integrated `Audit.lean` and the expected-axiom checker passed on all 870 registered declarations, with no `sorryAx`.

## What the recorded next step got wrong

The lane's recorded next step was "sector orthogonality", understood as

`∑ y : Fin (2·pc) → Bool, conj (psi_a y) * psi_a' y = 0` for `a ≠ a'`.

**That statement is false**, and it fails in an admitted case. At `pc = 0` the coordinate type `Fin 0 → Bool` is a singleton, the normalization is `2^0 = 1`, and each sector state is a sign; the "sum" is a single product `±1`, never zero. It is not only a rank-zero pathology: with `delta = R a + R a'` the summed phase is `f0 (x) + f0 (x + delta)` at `x = R a + D y`, and for the cubic `f0` there is no cancellation mechanism.

The manuscript's sectors are orthogonal for a different reason: they live on **disjoint affine cosets** of the character space, `im(D) + R a`. The honest statement is therefore about functions on the character space, and it is termwise.

## What was proved

New module `SectorSimulation/WalshSectorOrthogonal.lean`:

- `sectorAmplitude`: the sector state extended by zero off its coset, with the value at a character taken at a classically chosen coordinate tuple.
- `sectorAmplitude_support`: on its coset it is the sector state. The chosen witness is unique by the point-map injectivity proved in the previous increment.
- `sectorAmplitude_eq_zero_of_not_support`: off its coset it is zero.
- `sectorAmplitude_disjoint`: distinct labels give disjoint supports, because the annihilator recovers the label from any support point.
- `sectorStates_orthogonal`: `∑ l : BinaryVector n, star (psi_a l) * psi_a' l = 0` for `a ≠ a'`, termwise.

The statement was frozen in the planning lane and reviewed twice before any code (`kimi-k3.1-pro`, `deepseek-v4-pro`). Both confirmed the counterexample independently — one supplying a second, higher-rank example with overlap `1/2` — and both approved the disjoint-support replacement. The changes they required were applied: record the refutation so no future session re-derives the false reading, state the quotient-level disjointness before introducing the extension, and keep conjugation and the Hermitian inner product out of this increment except in the final termwise sum.

Scope must be read narrowly. This is a structural statement about the computed cosets. It does not identify them with the manuscript's sectors, which needs the rank bridge `hbound : n ≤ fuel`, the pairing symmetry and invertibility, and the cubic phases. The amplitudes never enter the disjointness argument, so nothing here validates the phase. The offset structure `eta = C l0`, the symmetry `X_a = X_(a+eta)`, the sector average `1 - 2p`, the Clifford observable, the matched vector and the overlap clauses all remain absent. No published theorem is certified; all seven labels remain `planned`.
