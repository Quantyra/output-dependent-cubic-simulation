import SectorSimulation.WalshSector
import SectorSimulation.WalshSectorNorm
import SectorSimulation.WalshSectorSupport
import SectorSimulation.WalshSectorOrthogonal
import SectorSimulation.HadamardWalshCoefficient
import SectorSimulation.ComplexSemantics

/-!
# The character-space sector vector and the diagonal phase factor

The observable layer begins here, and this module is deliberately narrow. The manuscript's observable
is `O = F_J D_f1 F_J Z_e F_J D_f1 F_J`, and the hard statement is `O_a psi_a = e^(i theta_a) psi_(a+eta)`
at the paper `2^(-n/2)` normalization; that needs the Gauss-sum evaluation and is the recorded first
unsupported implication of the layer. None of it is attempted here.

What this module does is the two things that must exist before the observable can even be written
down:

1. the sector state lifted to the character space, where `F_J` can act on it, is still a unit vector;
2. `D_f1`, the diagonal phase factor, is defined on character-space vectors, and the facts that it
   cannot move a sector's support or change its norm are recorded.

Both are helper-level statements about the formalization's own objects. `D_f1` preserves the norm for
*any* phase, so nothing here certifies the phase, and nothing here is a step of the paper's matched
sector computation.
-/

namespace SectorSimulation

open scoped BigOperators

/-- The point map is injective at a fixed sector label. -/
theorem sectorSupportPoint_injective_at_label {n : Nat}
    (q : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m)
    {y y' : Fin (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool}
    (h : sectorSupportPoint q fuel hdegree hlen m hsize hb a y =
      sectorSupportPoint q fuel hdegree hlen m hsize hb a y') :
    y = y' := by
  have hp : (a, y) = (a, y') :=
    sectorSupportPoint_injective q fuel hdegree hlen m hsize hb (by simpa using h)
  exact congrArg Prod.snd hp

/-- A signed complex number has the same squared modulus as the unsigned one. -/
theorem normSq_complexSigned (b : Bool) (z : ℂ) :
    Complex.normSq (complexSigned b z) = Complex.normSq z := by
  cases b <;> simp [complexSigned]

/-- Signing the exact zero gives the exact zero. -/
theorem exactSigned_zero (b : Bool) : exactSigned b exactZero = exactZero := by
  cases b <;> simp [exactSigned, exactNeg_zero]

/-- The unit-norm clause transported to the character space.

The character-space sum and the coordinate sum agree because the extension is zero off the coset and
the point map is injective at a fixed label. -/
theorem sectorAmplitude_sum_normSq {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) :
    (∑ l : BinaryVector n,
        Complex.normSq (exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l))) =
      (∑ y : (Fin (2 * (polarEliminate (phasePolar q) fuel
          (List.finRange n) identityMatrix).2.2.length) → Bool),
        Complex.normSq (exactComplex (sectorState q f0 J beta fuel hdegree hlen m hsize hb a y))) := by
  classical
  set f : BinaryVector n → ℝ := fun l =>
    Complex.normSq (exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l))
    with hf
  have hzero : ∀ l ∈ (Finset.univ : Finset (BinaryVector n)),
      l ∉ Finset.univ.image (fun y : (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool) =>
          sectorSupportPoint q fuel hdegree hlen m hsize hb a y) → f l = 0 := by
    intro l _ hl
    have hnot : ¬ ∃ y : (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool),
        sectorSupportPoint q fuel hdegree hlen m hsize hb a y = l := by
      intro hex
      obtain ⟨y, hy⟩ := hex
      exact hl (Finset.mem_image.mpr ⟨y, Finset.mem_univ y, hy⟩)
    show Complex.normSq (exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l)) = 0
    rw [sectorAmplitude_eq_zero_of_not_support q f0 J beta fuel hdegree hlen m hsize hb a l hnot]
    rw [exactComplex_zero]
    simp
  have h1 : (Finset.univ.sum f) =
      ∑ l ∈ Finset.univ.image (fun y : (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool) =>
          sectorSupportPoint q fuel hdegree hlen m hsize hb a y), f l :=
    (Finset.sum_subset (s₁ := Finset.univ.image (fun y : (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool) =>
          sectorSupportPoint q fuel hdegree hlen m hsize hb a y))
      (s₂ := (Finset.univ : Finset (BinaryVector n))) (Finset.subset_univ _) hzero).symm
  have h2 : (∑ l ∈ Finset.univ.image (fun y : (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool) =>
          sectorSupportPoint q fuel hdegree hlen m hsize hb a y), f l) =
      ∑ y : (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool),
        f (sectorSupportPoint q fuel hdegree hlen m hsize hb a y) :=
    Finset.sum_image (fun y _ y' _ hyy' =>
      sectorSupportPoint_injective_at_label q fuel hdegree hlen m hsize hb a hyy')
  have h3 : (∑ y : (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool),
        f (sectorSupportPoint q fuel hdegree hlen m hsize hb a y)) =
      (∑ y : (Fin (2 * (polarEliminate (phasePolar q) fuel
          (List.finRange n) identityMatrix).2.2.length) → Bool),
        Complex.normSq (exactComplex (sectorState q f0 J beta fuel hdegree hlen m hsize hb a y))) := by
    refine Finset.sum_congr rfl (fun y _ => ?_)
    show Complex.normSq (exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a
      (sectorSupportPoint q fuel hdegree hlen m hsize hb a y))) = _
    rw [sectorAmplitude_support q f0 J beta fuel hdegree hlen m hsize hb a y]
  calc (∑ l : BinaryVector n,
        Complex.normSq (exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l)))
      = Finset.univ.sum f := rfl
    _ = _ := h1
    _ = _ := h2
    _ = _ := h3

/-- The character-space sector vector is a unit vector. -/
theorem sectorAmplitude_unit_norm {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) :
    (∑ l : BinaryVector n,
      Complex.normSq (exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l))) = 1 := by
  rw [sectorAmplitude_sum_normSq q f0 J beta fuel hdegree hlen m hsize hb a]
  exact sectorState_unit_norm q f0 J beta fuel hdegree hlen m hsize hb a

/-- The diagonal phase factor `D_f1` applied to a character-space vector.

This is the character-basis diagonal operator used in the manuscript's observable. Its action is to
multiply the amplitude at a character by the sign of the phase there. -/
noncomputable def sectorDiag {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (f1 : PhaseANF n) (J : BinaryMatrix n)
    (beta : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) : BinaryVector n → ExactAmplitude :=
  fun l => exactSigned (evalPhase f1 l)
    (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l)

/-- On the coset, the diagonal factor is the signed sector state. -/
theorem sectorDiag_support {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (f1 : PhaseANF n) (J : BinaryMatrix n)
    (beta : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m)
    (y : Fin (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) :
    sectorDiag q f0 f1 J beta fuel hdegree hlen m hsize hb a
      (sectorSupportPoint q fuel hdegree hlen m hsize hb a y) =
      exactSigned (evalPhase f1 (sectorSupportPoint q fuel hdegree hlen m hsize hb a y))
        (sectorState q f0 J beta fuel hdegree hlen m hsize hb a y) := by
  rw [sectorDiag, sectorAmplitude_support]

/-- Off the coset, the diagonal factor vanishes. -/
theorem sectorDiag_eq_zero_of_not_support {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (f1 : PhaseANF n) (J : BinaryMatrix n)
    (beta : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) (l : BinaryVector n)
    (h : ¬ ∃ y : Fin (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool,
      sectorSupportPoint q fuel hdegree hlen m hsize hb a y = l) :
    sectorDiag q f0 f1 J beta fuel hdegree hlen m hsize hb a l = exactZero := by
  rw [sectorDiag]
  rw [sectorAmplitude_eq_zero_of_not_support q f0 J beta fuel hdegree hlen m hsize hb a l h,
    exactSigned_zero]

/-- The diagonal factor does not change the amplitude's squared modulus. -/
theorem sectorDiag_normSq {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (f1 : PhaseANF n) (J : BinaryMatrix n)
    (beta : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) (l : BinaryVector n) :
    Complex.normSq (exactComplex (sectorDiag q f0 f1 J beta fuel hdegree hlen m hsize hb a l)) =
      Complex.normSq (exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l)) := by
  rw [sectorDiag, exactComplex_signed, normSq_complexSigned]

/-- The diagonal factor preserves the unit norm of the character-space sector vector.

This holds for any phase `f1`: the operator is a diagonal sign, which is unimodular. It therefore says
nothing about whether the phase is the manuscript's. -/
theorem sectorDiag_unit_norm {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (f1 : PhaseANF n) (J : BinaryMatrix n)
    (beta : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) :
    (∑ l : BinaryVector n,
      Complex.normSq (exactComplex (sectorDiag q f0 f1 J beta fuel hdegree hlen m hsize hb a l))) = 1 := by
  rw [Finset.sum_congr rfl (fun l _ =>
    sectorDiag_normSq q f0 f1 J beta fuel hdegree hlen m hsize hb a l)]
  exact sectorAmplitude_unit_norm q f0 J beta fuel hdegree hlen m hsize hb a

/-- Distinct sectors remain disjoint after the diagonal factor is applied. -/
theorem sectorDiag_disjoint {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (f1 : PhaseANF n) (J : BinaryMatrix n)
    (beta : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a a' : BinaryVector m) (hne : a ≠ a') (l : BinaryVector n) :
    sectorDiag q f0 f1 J beta fuel hdegree hlen m hsize hb a l = exactZero ∨
      sectorDiag q f0 f1 J beta fuel hdegree hlen m hsize hb a' l = exactZero := by
  rcases sectorAmplitude_disjoint q f0 J beta fuel hdegree hlen m hsize hb a a' hne l with h | h
  · left
    rw [sectorDiag, h, exactSigned_zero]
  · right
    rw [sectorDiag, h, exactSigned_zero]

end SectorSimulation
