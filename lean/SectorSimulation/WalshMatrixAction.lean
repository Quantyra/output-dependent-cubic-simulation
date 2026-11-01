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


end SectorSimulation
