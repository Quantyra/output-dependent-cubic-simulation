# GCP certification evidence: the sector support point is a bijective parametrization

Source/audit commit: `5e9600d4f88e24f854e9cc9e6ab67819e5ce6ff6`.

The exact Lean source archive is `support-5e9600d-source.tar` (SHA-256 `44f157d2d4d36911fdf13d30c3eb5f90476ff709882d4a7396298d80db322c94`, 1,871,360 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-01` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,252 jobs). Integrated `Audit.lean` and the expected-axiom checker passed on all 865 registered declarations, with no `sorryAx`.

New module `SectorSimulation/WalshSectorSupport.lean` closes the gap that both earlier reviews named: the unit-norm theorem was a statement about a formal index type, because nothing had shown that distinct indices name distinct points.

- `sectorSupportPoint`: the paper's sector support point `R a + D y`, as a formal coset representative. It is deliberately named so that it is not confused with the existing physical `supportPoint`, which is built from the source Walsh sum and needs `hbound`.
- `sectorState_eq_sectorSupportPoint`: the sector state is the exact normalization times the sign read at that point.
- `residualAnnihilator_vectorXor`, `vectorXor_zeroVector`: the annihilator is additive over xor.
- `residualAnnihilator_sectorSupportPoint`: the annihilator recovers the sector label from the point, so distinct labels give disjoint cosets.
- `supportCoordinates_injective`: the basis matrix is injective on the coordinate space, since every recorded coordinate is recovered from the image.
- `sectorSupportPoint_injective`, `sectorSupportPoint_surjective`, `sectorSupportPoint_bijective`: `(a, y) ↦ R a + D y` is a bijection from labels and coordinate tuples onto the character space.

The statement was frozen in the planning lane and reviewed twice before any code (`kimi-k3.1-pro`, `deepseek-v4-pro`). Both approved with changes and all were applied: name the object so it cannot be confused with the existing `supportPoint`; state injectivity about the point rather than about the state, which is not injective because distinct points can carry the same sign; and scope the receipt to the formal labels rather than the paper's eta-coset representatives. Both also required the two trivial xor facts that the argument needs, and one noted that the annihilator identity is `hdegree`-dependent because it invokes the right-inverse specification.

The first compile attempt failed twice on presentation, not mathematics: an unreduced beta-redex in the pair equality and a missing `change` before unfolding the definition; then the audit checker failed because its new expectation rows were written with unquoted set literals, which took one corrected re-run of the exact-source chain.

Scope must be read narrowly. Nothing here identifies `D`, `C` or `R` with the manuscript's objects. Nothing asserts orthogonality of sector states: distinct points are named distinctly, which makes an orthogonality statement statable, not proved. The numeric identifications `m = c = n - r` and the offset `eta = C l0` need the rank bridge with `hbound : n ≤ fuel` and are not part of this increment. No published theorem is certified and all seven labels remain `planned`.
