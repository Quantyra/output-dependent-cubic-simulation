import SectorSimulation.WalshSector
import SectorSimulation.WalshSectorNorm
import SectorSimulation.WalshSectorSupport

/-!
# Sector states have disjoint supports, hence are orthogonal

The recorded next step in the lane was "sector orthogonality". The obvious reading of that —
averaging `conj (psi_a y) * psi_a' y` over the shared coordinate index `y` — is **false**, and it
fails in an admitted case: at `pc = 0` the coordinate type `Fin 0 -> Bool` is a singleton, the
normalization is one, each sector state is a sign, and the "sum" is a single product that is never
zero. At larger rank the summed phase is `f0 (x) + f0 (x + delta)` for the cubic `f0`, which has no
cancellation mechanism either.

The manuscript's sectors are orthogonal because they live on **disjoint affine cosets** of the
character space, not because of character cancellation. This module states that: the sector state is
extended by zero off its coset, and distinct labels give disjoint supports. Orthogonality of the
resulting character-space vectors is then termwise.

Scope: this is a structural statement about the computed cosets. It does not identify them with the
manuscript's sectors, it says nothing about the phase (the amplitudes never enter the disjointness
argument), and the offset structure `eta = C l0`, the observable, the matched vector and the overlap
clauses remain absent.
-/

namespace SectorSimulation

open scoped BigOperators

/-- The sector state, extended by zero off its coset in the character space.

The value at a character is the sector amplitude at any coordinate tuple that maps to it; that
coordinate is chosen classically and is unique because the point map is injective at a fixed label. -/
noncomputable def sectorAmplitude {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a : BinaryVector m) : BinaryVector n → ExactAmplitude := by
  classical
  exact fun l =>
    if h : ∃ y : Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool,
        sectorSupportPoint q fuel hdegree hlen m hsize hb a y = l
    then sectorState q f0 J beta fuel hdegree hlen m hsize hb a (Classical.choose h)
    else exactZero

/-- On its own coset the extended sector state is the sector state. -/
theorem sectorAmplitude_support {n : Nat}
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
    sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a
      (sectorSupportPoint q fuel hdegree hlen m hsize hb a y) =
      sectorState q f0 J beta fuel hdegree hlen m hsize hb a y := by
  classical
  unfold sectorAmplitude
  have h : ∃ y' : Fin (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool,
      sectorSupportPoint q fuel hdegree hlen m hsize hb a y' =
        sectorSupportPoint q fuel hdegree hlen m hsize hb a y := ⟨y, rfl⟩
  rw [dif_pos h]
  congr 1
  have hpair : (a, Classical.choose h) = (a, y) := by
    apply sectorSupportPoint_injective q fuel hdegree hlen m hsize hb
    simpa using Classical.choose_spec h
  exact congrArg Prod.snd hpair

/-- Off its coset the extended sector state vanishes. -/
theorem sectorAmplitude_eq_zero_of_not_support {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
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
    sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l = exactZero := by
  classical
  unfold sectorAmplitude
  rw [dif_neg h]

/-- Distinct sector labels have disjoint supports: no character lies on both cosets.

The annihilator recovers the label from any support point, so a character in two cosets would have
two labels. -/
theorem sectorAmplitude_disjoint {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a a' : BinaryVector m) (hne : a ≠ a') (l : BinaryVector n) :
    sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l = exactZero ∨
      sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a' l = exactZero := by
  classical
  by_cases ha : ∃ y : Fin (2 * (polarEliminate (phasePolar q) fuel
      (List.finRange n) identityMatrix).2.2.length) → Bool,
      sectorSupportPoint q fuel hdegree hlen m hsize hb a y = l
  · right
    by_cases ha' : ∃ y : Fin (2 * (polarEliminate (phasePolar q) fuel
        (List.finRange n) identityMatrix).2.2.length) → Bool,
        sectorSupportPoint q fuel hdegree hlen m hsize hb a' y = l
    · exfalso
      obtain ⟨y, hy⟩ := ha
      obtain ⟨y', hy'⟩ := ha'
      have h1 : residualAnnihilator m q fuel hlen hsize l = a := by
        rw [← hy]
        exact residualAnnihilator_sectorSupportPoint q fuel hdegree hlen m hsize hb a y
      have h2 : residualAnnihilator m q fuel hlen hsize l = a' := by
        rw [← hy']
        exact residualAnnihilator_sectorSupportPoint q fuel hdegree hlen m hsize hb a' y'
      exact hne (h1.symm.trans h2)
    · exact sectorAmplitude_eq_zero_of_not_support q f0 J beta fuel hdegree hlen m hsize hb a' l ha'
  · left
    exact sectorAmplitude_eq_zero_of_not_support q f0 J beta fuel hdegree hlen m hsize hb a l ha

/-- Sector states at distinct labels are orthogonal in the character space.

The sum is over all characters, not over the shared coordinate index: the amplitudes are supported on
disjoint cosets, so every product is zero. -/
theorem sectorStates_orthogonal {n : Nat}
    (q : PhaseANF n) (f0 : PhaseANF n) (J : BinaryMatrix n) (beta : BinaryVector n)
    (fuel : Nat)
    (hdegree : phaseWithinDegree 2 q = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar q) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (a a' : BinaryVector m) (hne : a ≠ a') :
    (∑ l : BinaryVector n,
      star (exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a l)) *
        exactComplex (sectorAmplitude q f0 J beta fuel hdegree hlen m hsize hb a' l)) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro l _
  rcases sectorAmplitude_disjoint q f0 J beta fuel hdegree hlen m hsize hb a a' hne l with h | h
  · rw [h, exactComplex_zero, star_zero, zero_mul]
  · rw [h, exactComplex_zero, mul_zero]

end SectorSimulation
