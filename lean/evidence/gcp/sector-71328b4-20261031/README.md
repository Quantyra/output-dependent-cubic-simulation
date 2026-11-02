# GCP certification evidence: the sector state psi_a is defined

Source/audit commit: `71328b4d341a89bcfb0491a91d5bad0720bb3d18`.

The exact Lean source archive is `sector-71328b4-source.tar` (SHA-256 `aae562166e5e3e53020225ff733725998e9c1a78303b9a4e3d208776dca77a61`, 1,840,640 bytes). It contains tracked Lean sources and the exact audit checker, excluding prior evidence archives; its hash was checked on the builder.

The dedicated Google Cloud builder `quantyra-sector-lean-builder-01` used Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, and pinned Lake manifest SHA-256 `ab0911ef870c1e4193db513c9766a9be167085f6222f4381f7a2aae4a0094642`. Full `lake build` completed (2,250 jobs). Integrated `Audit.lean` and the exact expected-axiom checker passed.

This is the first sector-layer declaration in the development, and until now the layer did not exist at all: a search of all 210 Lean files had found no sector state, no Clifford observable and no `psi`. `sectorState` defines the paper's sector state in exact amplitudes,

`psi_a(y) = 2^(-r/2) · (-1)^( f0(R a + D y) + (J beta)·(R a + D y) )`,

from objects already proved here: the support coordinates `D y` and the right inverse `R a` that give the support point, the matrix pairing character `matrixPairingParity`, the first-phase evaluator `evalPhase`, and the exact dyadic `⟨cycloOne, pairCount⟩`, whose value is `2^(-pairCount)` and therefore `2^(-r/2)` because the rank is twice the pair count. `sectorState_eq` is the definitional unfolding lemma, recorded so later sector statements can rewrite without unfolding the definition.

The definition was frozen in the planning lane and then reviewed twice before any code, as the adopted protocol requires. Both independent reviews rejected the first draft, consistently and correctly: the sector label is a `BinaryVector m` rather than `n`; the right inverse returns a vector, so the outer `matrixApply` was a type error; the character is `J beta` rather than `beta`, since using `beta` would have silently dropped `J` and broken the shift symmetry downstream; `J` was missing entirely; and the hypothesis block `fuel/hlen/m/hsize/hb` was incomplete. Every correction is applied and both reviewers approved the corrected form.

Scope is definition-only and should be read that way. No theorem is claimed. In particular, no correspondence is asserted between this `psi_a` and the paper's own object: the formalization measures the rank and the basis through the computed polar elimination, so identifying them with the paper's `r`, `D`, `C` and `R` needs the rank identification (which requires `hbound : n ≤ fuel`, deliberately not a definition hypothesis), the pairing symmetry and invertibility, and the cubic phases. Those belong to the sector proposition, which remains `planned`. The Clifford observable `O_a`, the matched vector `u_a`, the overlap `X_a` and every one of its clauses are still absent; the estimator's draw variable still cannot be defined. The formalization matrix is still not proved identical to the paper literal `D`, the sector offset structure is not carried, the computability clause still has only two refined cost stages, and no published theorem is certified.
