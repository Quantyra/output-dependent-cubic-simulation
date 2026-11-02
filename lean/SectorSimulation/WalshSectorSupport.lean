import SectorSimulation.WalshSector
import SectorSimulation.WalshSectorNorm
import SectorSimulation.WalshBasis
import SectorSimulation.WalshMatrixAction
import SectorSimulation.WalshSignCoordinates
import SectorSimulation.InterleavedCanonicalSum

/-!
# The sector support point is a bijective parametrization

The sector state's support point is `R a + D y`. The unit-norm theorem proved this state has the
paper's normalization, but only for the formal index type `Fin (2 * pc) -> Bool`: nothing had shown
that distinct indices give distinct points, so the result could not yet be read as a statement about
a basis.

This module closes that gap at the level of the computed objects. `sectorSupportPoint` names the
point, `residualAnnihilator_sectorSupportPoint` shows the annihilator recovers the sector label from
it, and the pair `(a, y) |-> R a + D y` is proved bijective.

Scope, stated because it is easy to overread. The annihilator identity holds under the recorded
degree hypothesis `hdegree`, because it invokes the right-inverse specification. Nothing here
identifies `D`, `C` or `R` with the manuscript's objects, and nothing here asserts orthogonality of
sector states: distinct points are named distinctly, which is what makes an orthogonality statement
statable, not a proof of it. The numeric identifications `m = c = n - r` and the offset `eta = C l0`
need the rank bridge with `hbound : n <= fuel` and are not part of this increment.
-/

namespace SectorSimulation

open scoped BigOperators

/-- The paper's sector support point `R a + D y`, in the computed objects.

This is the formal coset representative. It is deliberately not the same object as the existing
`supportPoint`, which is the physical support point built from the source Walsh sum and needs the
rank bound `hbound`. -/
noncomputable def sectorSupportPoint {n : Nat}
    (q : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m)
    (y : Fin (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool) : BinaryVector n :=
  vectorXor (residualRightInverse m q fuel hlen hsize a)
    (matrixApply (supportBasisMatrix q fuel hdegree hlen m hsize hb) (extendCoordinates q fuel y))

/-- The sector state is the exact normalization times the sign read at the sector support point. -/
theorem sectorState_eq_sectorSupportPoint {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
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
    sectorState q f0 J beta fuel hdegree hlen m hsize hb a y =
      exactMul (exactOfDyadic ⟨cycloOne,
          (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length⟩)
        (exactSigned (Bool.xor
          (evalPhase f0 (sectorSupportPoint q fuel hdegree hlen m hsize hb a y))
          (matrixPairingParity J (sectorSupportPoint q fuel hdegree hlen m hsize hb a y) beta))
          exactOne) := by
  rw [sectorState_eq]
  rfl

/-- The annihilator is additive over the pointwise xor of characters. -/
theorem residualAnnihilator_vectorXor {n : Nat}
    (m : Nat) (p : PhaseANF n) (fuel : Nat)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (x y : BinaryVector n) :
    residualAnnihilator m p fuel hlen hsize (vectorXor x y) =
      vectorXor (residualAnnihilator m p fuel hlen hsize x)
        (residualAnnihilator m p fuel hlen hsize y) := by
  simp only [residualAnnihilator]
  exact recordedResidualLinearPart_vectorXor _ _ _ x y

/-- The annihilator is additive over the pointwise xor of characters. -/
theorem vectorXor_zeroVector {n : Nat} (x : BinaryVector n) :
    vectorXor x zeroVector = x := by
  funext i
  simp [vectorXor, zeroVector]

/-- A sector support point has the sector label as its residual image. -/
theorem residualAnnihilator_sectorSupportPoint {n : Nat}
    (q : PhaseANF n) (fuel : Nat)
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
    residualAnnihilator m q fuel hlen hsize
      (sectorSupportPoint q fuel hdegree hlen m hsize hb a y) = a := by
  classical
  rw [sectorSupportPoint, residualAnnihilator_vectorXor,
    residualRightInverse_spec q fuel hdegree hlen m hsize a]
  have hker : residualAnnihilator m q fuel hlen hsize
      (matrixApply (supportBasisMatrix q fuel hdegree hlen m hsize hb)
        (extendCoordinates q fuel y)) = zeroVector := by
    rw [residualAnnihilator, matrixApply_supportBasisMatrix_extend]
    exact (kernelCoordinateElement_spec q fuel hdegree hlen m hsize hb y).1
  rw [hker, vectorXor_zeroVector]

/-- The basis matrix is injective on the coordinate space: the recorded coordinates are recovered
from the image itself. -/
theorem supportCoordinates_injective {n : Nat}
    (q : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Function.Injective (fun y : Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool =>
      matrixApply (supportBasisMatrix q fuel hdegree hlen m hsize hb) (extendCoordinates q fuel y)) := by
  classical
  intro y y' h
  have hk : kernelCoordinateElement q fuel hdegree hlen m hsize hb y =
      kernelCoordinateElement q fuel hdegree hlen m hsize hb y' := by
    rw [← matrixApply_supportBasisMatrix_extend q fuel hdegree hlen m hsize hb y,
      ← matrixApply_supportBasisMatrix_extend q fuel hdegree hlen m hsize hb y']
    exact h
  funext i
  rw [← kernelCoordinateElement_coordinates q fuel hdegree hlen m hsize hb y i,
    ← kernelCoordinateElement_coordinates q fuel hdegree hlen m hsize hb y' i, hk]

/-- The sector support point parametrization is injective: distinct sector labels and distinct
coordinate tuples give distinct points. -/
theorem sectorSupportPoint_injective {n : Nat}
    (q : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Function.Injective (fun p : BinaryVector m × (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool) =>
      sectorSupportPoint q fuel hdegree hlen m hsize hb p.1 p.2) := by
  classical
  rintro ⟨a, y⟩ ⟨a', y'⟩ h
  simp only at h
  have ha : a = a' := by
    rw [← residualAnnihilator_sectorSupportPoint q fuel hdegree hlen m hsize hb a y,
      ← residualAnnihilator_sectorSupportPoint q fuel hdegree hlen m hsize hb a' y', h]
  subst ha
  have hy : y = y' := by
    apply supportCoordinates_injective q fuel hdegree hlen m hsize hb
    have h2 := congrArg (vectorXor (residualRightInverse m q fuel hlen hsize a)) h
    simpa only [sectorSupportPoint, vectorXor_cancel_left] using h2
  rw [hy]

/-- Every character is a sector support point: the annihilator recovers the label, and the residual
kernel is exactly the image of the basis. Hence the parametrization is bijective. -/
theorem sectorSupportPoint_surjective {n : Nat}
    (q : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Function.Surjective (fun p : BinaryVector m × (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool) =>
      sectorSupportPoint q fuel hdegree hlen m hsize hb p.1 p.2) := by
  classical
  intro l
  let a : BinaryVector m := residualAnnihilator m q fuel hlen hsize l
  have hmem : residualAnnihilator m q fuel hlen hsize
      (vectorXor l (residualRightInverse m q fuel hlen hsize a)) = zeroVector := by
    rw [residualAnnihilator_vectorXor,
      residualRightInverse_spec q fuel hdegree hlen m hsize a]
    exact (vectorXor_eq_zero_iff _ _).mpr rfl
  obtain ⟨y, hy⟩ := (supportBasisColumns_span_polarImage q fuel hdegree hlen m hsize hb
    (vectorXor l (residualRightInverse m q fuel hlen hsize a))).mp
      (by simpa only [residualAnnihilator] using hmem)
  refine ⟨(a, y), ?_⟩
  change sectorSupportPoint q fuel hdegree hlen m hsize hb a y = l
  rw [sectorSupportPoint, matrixApply_supportBasisMatrix_extend, hy,
    vectorXor_comm l (residualRightInverse m q fuel hlen hsize a)]
  exact vectorXor_cancel_left _ l

/-- The sector support point parametrization is a bijection from labels and coordinate tuples onto
the character space. -/
theorem sectorSupportPoint_bijective {n : Nat}
    (q : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Function.Bijective (fun p : BinaryVector m × (Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool) =>
      sectorSupportPoint q fuel hdegree hlen m hsize hb p.1 p.2) :=
  ⟨sectorSupportPoint_injective q fuel hdegree hlen m hsize hb,
    sectorSupportPoint_surjective q fuel hdegree hlen m hsize hb⟩

end SectorSimulation
