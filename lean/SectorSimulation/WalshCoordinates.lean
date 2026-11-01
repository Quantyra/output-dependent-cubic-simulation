import SectorSimulation.WalshClauses

/-!
# The support in the manuscript's coordinates

The Walsh lemma's support clause is stated in the manuscript as an affine image parametrized by
`r` coordinates. The formalization already has such a parametrization: the exact support is a
coset of the polar image, and the polar image is in bijection with assignments on the recorded
paired block, which has exactly the proved rank many entries.

This module packages that as a single coordinate equivalence and restates the support and
magnitude results through it, so they are stated in the manuscript's `r`-coordinate shape rather
than through `Fin (2 * pairCount) → Bool`. It does not yet express the sign's quadratic form in
those coordinates, and it certifies no published theorem.
-/

namespace SectorSimulation

open Classical

/-- The `r`-coordinate space of the exact source Walsh support: the recorded paired block, whose
size is the proved polar rank. -/
abbrev SupportCoordinateSpace {n : Nat} (p : PhaseANF n) (fuel : Nat) : Type :=
  Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) → Bool

/-- The exact source Walsh support, as a type. -/
abbrev SourceWalshSupport {n : Nat} (p : PhaseANF n) : Type :=
  {l : BinaryVector n // sourceWalshSum p l ≠ 0}

/-- The manuscript's coordinate parametrization of the exact source Walsh support: a supported
character is the base support point translated by the residual kernel element whose recorded
paired-block coordinates are the given `r`-tuple. -/
noncomputable def supportCoordinateEquiv {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    SourceWalshSupport p ≃ SupportCoordinateSpace p fuel := by
  classical
  -- step 1: translate the support onto the polar image
  let l₀ := Classical.choose (sourceWalshSum_support_nonempty p fuel hdegree hbound)
  have hl₀ : sourceWalshSum p l₀ ≠ 0 :=
    Classical.choose_spec (sourceWalshSum_support_nonempty p fuel hdegree hbound)
  let e₁ : SourceWalshSupport p ≃ Set.range (sourcePolarVector p) :=
    Equiv.mk
      (fun l => ⟨vectorXor l₀ l.1,
        (sourceWalshSum_support_polar_coset p fuel hdegree hbound hlen m hsize l₀ l.1 hl₀).mp l.2⟩)
      (fun v => ⟨vectorXor l₀ v.1, by
        obtain ⟨x, hx⟩ := v.2
        refine (sourceWalshSum_support_polar_coset p fuel hdegree hbound hlen m hsize l₀
          (vectorXor l₀ v.1) hl₀).mpr ⟨x, ?_⟩
        rw [hx, vectorXor_cancel_left]⟩)
      (by
        intro l
        apply Subtype.ext
        dsimp only
        exact vectorXor_cancel_left l₀ l.1)
      (by
        intro v
        apply Subtype.ext
        dsimp only
        exact vectorXor_cancel_left l₀ v.1)
  -- step 2: the polar image is the residual kernel
  have hset : Set.range (sourcePolarVector p) =
      {l : BinaryVector n |
        recordedResidualLinearPart
          (recordedCoordinateAt
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
          hsize
          (transposeBinaryMatrix
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector} := by
    ext l
    rw [Set.mem_range]
    exact (residualKernel_eq_sourcePolarImage p fuel hdegree hbound hlen m hsize l).symm
  let e₂ : Set.range (sourcePolarVector p) ≃
      {l : BinaryVector n |
        recordedResidualLinearPart
          (recordedCoordinateAt
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
          hsize
          (transposeBinaryMatrix
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector} :=
    Equiv.setCongr hset
  -- step 3: the kernel is the coordinate space
  let e₃ : {l : BinaryVector n |
        recordedResidualLinearPart
          (recordedCoordinateAt
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
          hsize
          (transposeBinaryMatrix
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1) l = zeroVector} ≃
      SupportCoordinateSpace p fuel :=
    Equiv.ofBijective _ (residualKernel_pairedBlock_bijective p fuel hdegree hlen m hsize hb)
  exact e₁.trans (e₂.trans e₃)

/-- The support point carrying a given `r`-tuple of coordinates. -/
noncomputable def supportPoint {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : SupportCoordinateSpace p fuel) : BinaryVector n :=
  (supportCoordinateEquiv p fuel hdegree hbound hlen m hsize hb).symm y |>.1

/-- Every coordinate tuple labels a supported character. -/
theorem sourceWalshSum_supportPoint_ne_zero {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : SupportCoordinateSpace p fuel) :
    sourceWalshSum p (supportPoint p fuel hdegree hbound hlen m hsize hb y) ≠ 0 :=
  (supportCoordinateEquiv p fuel hdegree hbound hlen m hsize hb).symm y |>.2

/-- The support is exactly the image of the coordinate space: this is the manuscript's affine
support parametrization stated through the proved rank many coordinates. -/
theorem sourceWalshSum_support_iff_coordinates {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (l : BinaryVector n) :
    sourceWalshSum p l ≠ 0 ↔ ∃ y : SupportCoordinateSpace p fuel,
      supportPoint p fuel hdegree hbound hlen m hsize hb y = l := by
  constructor
  · intro hl
    exact ⟨(supportCoordinateEquiv p fuel hdegree hbound hlen m hsize hb) ⟨l, hl⟩, by
      simp [supportPoint]⟩
  · rintro ⟨y, rfl⟩
    exact sourceWalshSum_supportPoint_ne_zero p fuel hdegree hbound hlen m hsize hb y

/-- The magnitude clause on the coordinate parametrization: every supported character has
magnitude two to the dimension less the polar rank over two. -/
theorem sourceWalshSum_supportPoint_natAbs {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : SupportCoordinateSpace p fuel) :
    Int.natAbs (sourceWalshSum p (supportPoint p fuel hdegree hbound hlen m hsize hb y)) =
      2 ^ (n - Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) / 2) :=
  sourceWalshSum_support_natAbs_rank p _ fuel hdegree hbound hlen m hsize hb
    (sourceWalshSum_supportPoint_ne_zero p fuel hdegree hbound hlen m hsize hb y)

end SectorSimulation
