import SectorSimulation.WalshMatrix

/-!
# The basis matrix applied to the padded tuple

This module proves the action identity for the explicit basis matrix: applying `supportBasisMatrix`
to a padded coordinate tuple returns the coordinate element, the annihilator kills that result,
and the exact support is the affine image of the matrix.

The proof runs through the Boolean sum calculus already in the development: matrix application is
a Boolean sum of column entries, `&&` distributes over such sums, `booleanListSum_swap` swaps the
resulting double sum, and `booleanListSum_singleton` collapses the Kronecker term. Working with the
full `n`-indexed columns, whose entries past the pair count are zero, avoids any reindexing between
`Fin n` and `Fin (2 * pairCount)`.
-/

namespace SectorSimulation

open Classical

/-- Matrix application is a Boolean sum of column entries weighted by the argument. -/
theorem matrixApply_eq_booleanListSum {n : Nat} (J : BinaryMatrix n) (z : BinaryVector n)
    (i : Fin n) :
    matrixApply J z i = booleanListSum (List.finRange n) (fun j => J i j && z j) := by
  unfold matrixApply
  rw [xorFoldl_as_sum]
  cases booleanListSum (List.finRange n) (fun j => J i j && z j) <;> rfl

/-- A constant `&&` distributes out of a Boolean sum. -/
theorem booleanListSum_and_left {α : Type} (xs : List α) (a : Bool) (f : α → Bool) :
    booleanListSum xs (fun x => a && f x) = (a && booleanListSum xs f) := by
  induction xs with
  | nil => cases a <;> rfl
  | cons x rest ih =>
      change Bool.xor (a && f x) (booleanListSum rest (fun x => a && f x)) =
        (a && Bool.xor (f x) (booleanListSum rest f))
      rw [ih]
      cases a <;> cases (f x) <;> cases (booleanListSum rest f) <;> rfl

/-- A constant `&&` distributes out of a Boolean sum on the right. -/
theorem booleanListSum_and_right {α : Type} (xs : List α) (a : Bool) (f : α → Bool) :
    booleanListSum xs (fun x => f x && a) = (booleanListSum xs f && a) := by
  induction xs with
  | nil => cases a <;> rfl
  | cons x rest ih =>
      change Bool.xor (f x && a) (booleanListSum rest (fun x => f x && a)) =
        (Bool.xor (f x) (booleanListSum rest f) && a)
      rw [ih]
      cases a <;> cases (f x) <;> cases (booleanListSum rest f) <;> rfl

/-- The `l`-th full column of the basis matrix: the basis column for `l` below the pair count
and the zero vector past it. -/
noncomputable def supportBasisColumnN {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (l : Fin n) : BinaryVector n :=
  if h : l.val < 2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length then
    supportBasisColumn p fuel hdegree hlen m hsize hb ⟨l.val, h⟩
  else zeroVector

/-- The columns of the basis matrix are the full columns. -/
theorem supportBasisMatrix_apply_column {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (i l : Fin n) :
    supportBasisMatrix p fuel hdegree hlen m hsize hb i l =
      supportBasisColumnN p fuel hdegree hlen m hsize hb l i := by
  unfold supportBasisMatrix supportBasisColumnN
  by_cases h : l.val < 2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    rfl

/-- The transformed full column is the paired-block extension of the corresponding unit tuple, or
zero past the pair count. -/
theorem transpose_supportBasisColumnN {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (l : Fin n) :
    matrixApply (transposeBinaryMatrix
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
      (supportBasisColumnN p fuel hdegree hlen m hsize hb l) =
      if h : l.val < 2 * (polarEliminate (phasePolar p) fuel
          (List.finRange n) identityMatrix).2.2.length then
        pairedBlockExtend (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
          hlen hb (fun i => decide (i.val = l.val))
      else zeroVector := by
  classical
  unfold supportBasisColumnN
  by_cases h : l.val < 2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length
  · rw [dif_pos h, dif_pos h]
    have : (⟨l.val, h⟩ : Fin (2 * (polarEliminate (phasePolar p) fuel
        (List.finRange n) identityMatrix).2.2.length)) = ⟨l.val, h⟩ := rfl
    rw [show supportBasisColumn p fuel hdegree hlen m hsize hb ⟨l.val, h⟩ =
        kernelCoordinateElement p fuel hdegree hlen m hsize hb
          (fun i => decide (i = ⟨l.val, h⟩)) from rfl]
    rw [transpose_kernelCoordinateElement p fuel hdegree hlen m hsize hb]
    congr 1
    funext i
    exact decide_eq_decide.mpr Fin.ext_iff
  · rw [dif_neg h, dif_neg h, matrixApply_zero]


/-! ## The action identity -/

/-- The transformed matrix product at any index is the Boolean sum of the transformed full
columns weighted by the padded tuple. -/
theorem transpose_matrixApply_supportBasisMatrix_extend {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) → Bool) (j : Fin n) :
    matrixApply
        (transposeBinaryMatrix (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
        (matrixApply (supportBasisMatrix p fuel hdegree hlen m hsize hb)
          (extendCoordinates p fuel y)) j =
      booleanListSum (List.finRange n) (fun l =>
        (if h : l.val < 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length then
            pairedBlockExtend (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb (fun i => decide (i.val = l.val))
          else zeroVector) j &&
        (extendCoordinates p fuel y) l) := by
  classical
  rw [matrixApply_eq_booleanListSum]
  trans booleanListSum (List.finRange n) (fun i =>
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 i j &&
        booleanListSum (List.finRange n) (fun l =>
          supportBasisColumnN p fuel hdegree hlen m hsize hb l i &&
            (extendCoordinates p fuel y) l))
  · apply booleanListSum_congr
    intro i _
    rw [matrixApply_eq_booleanListSum]
    apply congrArg (fun b => (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 i j && b)
    apply booleanListSum_congr
    intro l _
    rw [supportBasisMatrix_apply_column]
  trans booleanListSum (List.finRange n) (fun i =>
      booleanListSum (List.finRange n) (fun l =>
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 i j &&
          (supportBasisColumnN p fuel hdegree hlen m hsize hb l i &&
            (extendCoordinates p fuel y) l)))
  · apply booleanListSum_congr
    intro i _
    rw [← booleanListSum_and_left]
  trans booleanListSum (List.finRange n) (fun i =>
      booleanListSum (List.finRange n) (fun l =>
        ((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 i j && supportBasisColumnN p fuel hdegree hlen m hsize hb l i) &&
          (extendCoordinates p fuel y) l))
  · apply booleanListSum_congr
    intro i _
    apply booleanListSum_congr
    intro l _
    rw [← Bool.and_assoc]
  trans booleanListSum (List.finRange n) (fun l =>
      booleanListSum (List.finRange n) (fun i =>
        ((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 i j && supportBasisColumnN p fuel hdegree hlen m hsize hb l i) &&
          (extendCoordinates p fuel y) l))
  · rw [booleanListSum_swap]
  trans booleanListSum (List.finRange n) (fun l =>
      (booleanListSum (List.finRange n) (fun i =>
        (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 i j && supportBasisColumnN p fuel hdegree hlen m hsize hb l i)) &&
        (extendCoordinates p fuel y) l)
  · apply booleanListSum_congr
    intro l _
    rw [booleanListSum_and_right]
  · apply booleanListSum_congr
    intro l _
    rw [show booleanListSum (List.finRange n)
        (fun i => (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1 i j && supportBasisColumnN p fuel hdegree hlen m hsize hb l i) =
        matrixApply (transposeBinaryMatrix (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
          (supportBasisColumnN p fuel hdegree hlen m hsize hb l) j from
      (matrixApply_eq_booleanListSum (transposeBinaryMatrix (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
        (supportBasisColumnN p fuel hdegree hlen m hsize hb l) j).symm]
    rw [transpose_supportBasisColumnN p fuel hdegree hlen m hsize hb l]

/-- Applying the basis matrix to the padded tuple returns the coordinate element. -/
theorem matrixApply_supportBasisMatrix_extend {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) → Bool) :
    matrixApply (supportBasisMatrix p fuel hdegree hlen m hsize hb)
        (extendCoordinates p fuel y) =
      kernelCoordinateElement p fuel hdegree hlen m hsize hb y := by
  classical
  obtain ⟨ts, _, _, hpolar, halt, _, _⟩ := sourceQuadratic_hasPolar p hdegree
  have hl0 : ∀ z, phasePolar p z z = false := by
    intro z
    rw [hpolar]
    exact halt z
  have hdp := polarEliminate_distinct_pairs (phasePolar p) fuel (List.finRange n)
    identityMatrix hl0
  have hinj := matrixApply_transpose_injective_of_surjective (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1
    (polarEliminate_surjective (phasePolar p) fuel (List.finRange n))
  apply hinj
  rw [transpose_kernelCoordinateElement p fuel hdegree hlen m hsize hb y]
  funext j
  rw [transpose_matrixApply_supportBasisMatrix_extend p fuel hdegree hlen m hsize hb y j]
  obtain (⟨tr, htlt, ht⟩ | hunp) :=
    recordedIndex_paired_or_unpaired (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hdp.1 hdp.2 hlen hsize j
  · rw [← ht, ← recordedPairedPos_eq_recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb tr htlt]
    rw [pairedBlockExtend_apply (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hdp.1 hdp.2 hlen hb y ⟨tr.val, htlt⟩]
    trans booleanListSum (List.finRange n) (fun l =>
        decide (l = tr) && extendCoordinates p fuel y l)
    · apply booleanListSum_congr
      intro l _
      by_cases h : l.val < 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length
      · rw [dif_pos h]
        rw [pairedBlockExtend_apply (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2
          hdp.1 hdp.2 hlen hb (fun i => decide (i.val = l.val)) ⟨tr.val, htlt⟩]
        exact congrArg (fun b => (b && extendCoordinates p fuel y l))
          (decide_eq_decide.mpr (show (tr.val = l.val) ↔ (l = tr) from by
            constructor
            · intro he
              exact Fin.ext (by rw [he])
            · intro he
              rw [he]))
      · rw [dif_neg h]
        have hne : ¬ (l = tr) := by
          intro he
          have hv : l.val = tr.val := by rw [he]
          omega
        rw [decide_eq_false_iff_not.mpr hne]
        simp [zeroVector]
    · rw [booleanListSum_singleton (List.finRange n) tr
        (extendCoordinates p fuel y) (List.nodup_finRange n),
        if_pos (List.mem_finRange tr)]
      rw [extendCoordinates, dif_pos htlt]
  · rw [pairedBlockExtend_unpaired (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb y j hunp]
    trans booleanListSum (List.finRange n) (fun _ => false)
    · apply booleanListSum_congr
      intro l _
      by_cases h : l.val < 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length
      · rw [dif_pos h]
        rw [pairedBlockExtend_unpaired (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen hb
          (fun i => decide (i.val = l.val)) j hunp]
        rfl
      · rw [dif_neg h]
        rfl
    · exact booleanListSum_const_false _


/-- The annihilator kills the basis matrix image of every padded coordinate tuple. -/
theorem supportBasisMatrix_extend_annihilated {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) → Bool) :
    recordedResidualLinearPart
      (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize
      (transposeBinaryMatrix (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
      (matrixApply (supportBasisMatrix p fuel hdegree hlen m hsize hb)
        (extendCoordinates p fuel y)) = zeroVector := by
  rw [matrixApply_supportBasisMatrix_extend p fuel hdegree hlen m hsize hb y]
  exact kernelCoordinateElement_mem p fuel hdegree hlen m hsize hb y

/-- The exact source Walsh support is the affine image of the basis matrix: the matrix form of
`l0 + im(D)`. -/
theorem sourceWalshSum_support_matrix {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (hbound : n ≤ fuel)
    (l₀ : BinaryVector n) (hl₀ : sourceWalshSum p l₀ ≠ 0) (l : BinaryVector n) :
    sourceWalshSum p l ≠ 0 ↔
      ∃ y : Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) → Bool,
        l = vectorXor l₀ (matrixApply (supportBasisMatrix p fuel hdegree hlen m hsize hb)
          (extendCoordinates p fuel y)) := by
  classical
  have hstep : ∀ y : Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) → Bool,
      matrixApply (supportBasisMatrix p fuel hdegree hlen m hsize hb)
        (extendCoordinates p fuel y) = kernelCoordinateElement p fuel hdegree hlen m hsize hb y :=
    fun y => matrixApply_supportBasisMatrix_extend p fuel hdegree hlen m hsize hb y
  constructor
  · intro hl
    obtain ⟨x, hx⟩ :=
      (sourceWalshSum_support_polar_coset p fuel hdegree hbound hlen m hsize l₀ l hl₀).mp hl
    have hker : recordedResidualLinearPart
        (recordedCoordinateAt (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2 hlen) hsize (transposeBinaryMatrix (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).1)
          (vectorXor l₀ l) = zeroVector :=
      (residualKernel_eq_sourcePolarImage p fuel hdegree hbound hlen m hsize
        (vectorXor l₀ l)).mpr ⟨x, hx⟩
    obtain ⟨y, hy⟩ :=
      (supportBasisColumns_span_polarImage p fuel hdegree hlen m hsize hb
        (vectorXor l₀ l)).mp hker
    refine ⟨y, ?_⟩
    rw [hstep y, hy, vectorXor_cancel_left]
  · rintro ⟨y, rfl⟩
    have hmem := kernelCoordinateElement_mem p fuel hdegree hlen m hsize hb y
    obtain ⟨x, hx⟩ := (residualKernel_eq_sourcePolarImage p fuel hdegree hbound hlen m hsize
      (kernelCoordinateElement p fuel hdegree hlen m hsize hb y)).mp hmem
    refine (sourceWalshSum_support_polar_coset p fuel hdegree hbound hlen m hsize l₀
      (vectorXor l₀ (matrixApply (supportBasisMatrix p fuel hdegree hlen m hsize hb)
        (extendCoordinates p fuel y))) hl₀).mpr ⟨x, ?_⟩
    rw [vectorXor_cancel_left, hstep y]
    exact hx

end SectorSimulation
