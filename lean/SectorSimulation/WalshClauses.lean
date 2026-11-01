import SectorSimulation.WalshRank

/-!
# The Walsh lemma clauses in terms of the proved polar rank

`SectorSimulation.WalshRank` identifies the manuscript's polar rank with twice the recorded
polar-elimination pair count, as a theorem about `Module.finrank` over the two-element field.
This module restates the four rank-dependent clauses of the paper's Walsh lemma in terms of that
rank: rank evenness, the support dimension, the normalized magnitude `2 ^ (n - r / 2)`, and the
quadratic sign, whose coordinate count is `r / 2`.

These are statement restatements, not new mathematics: each is assembled from a result already
kernel checked in the development plus the proved rank identification. They do not connect the
formalization's paired-block coordinates to the paper's own support basis matrix, do not supply
the computability clause's bit-operation cost trace, and certify no published theorem.
-/

namespace SectorSimulation

open Classical

/-- The manuscript's polar rank is even. This is the rank-evenness clause of the paper's Walsh
lemma stated through the proved identification of the rank with twice the pair count. -/
theorem polarRank_even_nat {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Even (Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree))) := by
  rw [polarRank_eq_two_mul p fuel hdegree hbound hlen m hsize hb]
  exact ⟨_, Nat.two_mul _⟩

/-- The exact source Walsh support has cardinality two to the proved polar rank: the
support-dimension clause of the paper's Walsh lemma, stated through the rank. -/
theorem sourceWalshSupport_card_eq_two_pow_rank {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    Fintype.card {l : BinaryVector n // sourceWalshSum p l ≠ 0} =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) := by
  classical
  obtain ⟨l₀, hl₀⟩ := sourceWalshSum_support_nonempty p fuel hdegree hbound
  let f : {l : BinaryVector n // sourceWalshSum p l ≠ 0} → Set.range (sourcePolarVector p) :=
    fun l => ⟨vectorXor l₀ l.1,
      (sourceWalshSum_support_polar_coset p fuel hdegree hbound hlen m hsize l₀ l.1 hl₀).mp l.2⟩
  let g : Set.range (sourcePolarVector p) → {l : BinaryVector n // sourceWalshSum p l ≠ 0} :=
    fun v => ⟨vectorXor l₀ v.1, by
      obtain ⟨x, hx⟩ := v.2
      refine (sourceWalshSum_support_polar_coset p fuel hdegree hbound hlen m hsize l₀
        (vectorXor l₀ v.1) hl₀).mpr ⟨x, ?_⟩
      rw [hx, vectorXor_cancel_left]⟩
  have hgf : ∀ v, f (g v) = v := by
    intro v
    apply Subtype.ext
    dsimp only [f, g]
    exact vectorXor_cancel_left l₀ v.1
  have hfg : ∀ l, g (f l) = l := by
    intro l
    apply Subtype.ext
    dsimp only [f, g]
    exact vectorXor_cancel_left l₀ l.1
  calc Fintype.card {l : BinaryVector n // sourceWalshSum p l ≠ 0}
      = Fintype.card (Set.range (sourcePolarVector p)) :=
        Fintype.card_congr (Equiv.mk f g hfg hgf)
    _ = 2 ^ (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) :=
        sourcePolarImage_card_eq_two_pow p fuel hdegree hbound hlen m hsize hb
    _ = 2 ^ Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) := by
        rw [polarRank_eq_two_mul p fuel hdegree hbound hlen m hsize hb]
/-- Every nonzero exact source Walsh value has magnitude `2 ^ (n - r / 2)` for the proved polar
rank `r`: the magnitude clause of the paper's Walsh lemma, stated through the rank. -/
theorem sourceWalshSum_support_natAbs_rank {n : Nat}
    (p : PhaseANF n) (l : BinaryVector n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (hne : sourceWalshSum p l ≠ 0) :
    Int.natAbs (sourceWalshSum p l) =
      2 ^ (n - Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) / 2) := by
  rw [sourceWalshSum_support_natAbs p l fuel hdegree hbound hne]
  have hr := polarRank_eq_two_mul p fuel hdegree hbound hlen m hsize hb
  rw [hr, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- The support sign is the recorded constant xored with the parity of the products of
`r / 2` canonical coordinate pairs, for the proved polar rank `r`: the quadratic-sign clause of
the paper's Walsh lemma, stated through the rank. -/
theorem sourceWalshSupportSign_quadratic_rank {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true) (hbound : n ≤ fuel)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (J : BinaryMatrix n) (l : BinaryVector n) :
    sourceWalshSupportSign p
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize J l =
      Bool.xor
        (Bool.xor (evalPhase p (fun _ => false))
          (evalPhase (recordedPairPhase
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) (fun _ => false)))
        (booleanListSum (List.finRange
          (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) (fun i =>
          canonicalLeft (coordinateReindex (@interleavedIndexFromCanonical
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length m)
            (binaryVectorCast hsize (coordinateReindex (recordedCoordinateAt
              (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
              (binaryShift (fun i => normalizedDifference
                (fun y => evalPhase p (matrixApply J y))
                (fun x => evalPhase (recordedPairPhase
                  (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) x)
                (coordinateUnit i))
                (matrixApply (transposeBinaryMatrix J) l))))) i &&
          canonicalRight (coordinateReindex (@interleavedIndexFromCanonical
            (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length m)
            (binaryVectorCast hsize (coordinateReindex (recordedCoordinateAt
              (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen)
              (binaryShift (fun i => normalizedDifference
                (fun y => evalPhase p (matrixApply J y))
                (fun x => evalPhase (recordedPairPhase
                  (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2) x)
                (coordinateUnit i))
                (matrixApply (transposeBinaryMatrix J) l))))) i)) ∧
      2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length =
        Module.finrank (ZMod 2) (LinearMap.range (polarLinearMap p hdegree)) := by
  constructor
  · exact sourceWalshSupportSign_as_quadratic
      (k := (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length)
      p (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hsize rfl J l
  · exact (polarRank_eq_two_mul p fuel hdegree hbound hlen m hsize hb).symm

end SectorSimulation
