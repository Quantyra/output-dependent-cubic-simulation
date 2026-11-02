# GCP certification evidence: the sector state is a unit vector

Source/audit commit: `4e8f07a42d00c16be0d1cbf0e22b1db540df2533`.

The exact Lean source archive is `unit-norm-4e8f07a-source.tar` (SHA-256 `dd732fd58feba8b40374928114ce22b1e9b5a93245882bedaadc5296b1226105`, 1,851,392 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-01` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,251 jobs). Integrated `Audit.lean` and the expected-axiom checker passed on all 856 registered declarations, with no `sorryAx`.

New module `SectorSimulation/WalshSectorNorm.lean` proves the paper's first assertion about the sector state: summing the squared moduli of the exact amplitudes over the coordinate index gives one.

- `sectorState_unit_norm`: for every admitted source and every sector label `a`, `∑ y, normSq (exactComplex (sectorState … a y)) = 1`.
- `sectorState_normSq`: every single amplitude has squared modulus `2^(-2·pc)`.
- `exactComplex_dyadicPow`: the exact dyadic `2^(-k)` read in `ℂ` is `1 / 2^k`.
- `normSq_complexSigned_one`, `normSq_exactComplex_signed_one`: a sign has unit squared modulus.

The reason the clause closes without square roots is that the sector rank is `r = 2·pc`, so the normalization `2^(-r/2)` is the dyadic `2^(-pc)`: each of the `2^(2·pc)` coordinate tuples contributes `2^(-2·pc)`.

Scope must be read narrowly, and the independent reviews insisted on saying so. The modulus is phase independent — the sign cancels — so this certifies normalization, not the phase. It says nothing about the paper's own `psi_a`: identifying this object with the manuscript's sector state is the sector proposition's job and still requires the rank identification with `hbound : n ≤ fuel`, the pairing symmetry and invertibility, and the cubic phases. It also does not prove that `y ↦ R a + D y` is injective, so the result is a statement about the `y`-indexed amplitude vector, not yet about a vector in a physical sector basis.

The statement was frozen in the planning lane and reviewed twice before any code (`kimi-k3.1-pro`, `deepseek-v4-pro`). Both approved with changes, and both changes were needed: the reviews required recording the phase-independence and index-level caveats, and predicted that the real-to-complex coercion and a missing import were the likely compile failures. The missing `ComplexSemantics` import was in fact the first failure, and the exponent rewrite was the second.

Still absent: the Clifford observable `O_a`, the matched vector `u_a`, the overlap `X_a` and every clause about it, the estimator statements, the paper literal `D` identification, the sector offset structure, and the computability clause beyond its present cost stages. All seven published theorem labels remain `planned`; nothing in this receipt certifies a manuscript theorem.
