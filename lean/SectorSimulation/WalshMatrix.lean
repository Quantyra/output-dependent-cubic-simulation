import SectorSimulation.WalshSignCoordinates

/-!
# The manuscript basis matrix as an explicit object

`WalshBasis` supplies the polar image as a family of basis columns, with the annihilator `C` and a
right inverse `R`. The manuscript writes an explicit matrix `D`. This module builds that object:
an `n`-by-`n` binary matrix whose first `2 * pairCount` columns are the basis columns and whose
remaining columns are zero, together with the padded coordinate tuple it acts on.

It records that the matrix columns are the basis columns, that applying the matrix is the fold of
its columns, and that on a padded unit tuple the matrix returns the corresponding basis column,
which the annihilator kills. The general tuple identity needs the Boolean fold-distribution lemma
noted in the module documentation of `WalshBasis`; it is the next step.
-/

namespace SectorSimulation

open Classical

/-- A left fold of pointwise XOR over a finite list of binary vectors. -/
def vectorFoldlXor {n : Nat} (vs : List (BinaryVector n)) : BinaryVector n :=
  vs.foldl (fun acc v => vectorXor acc v) zeroVector

/-- Reading a folded XOR at one coordinate is the Boolean fold of the coordinate readings. -/
theorem vectorFoldlXor_apply {n : Nat} (vs : List (BinaryVector n)) (i : Fin n) :
    vectorFoldlXor vs i = vs.foldl (fun acc v => Bool.xor acc (v i)) false := by
  have key : ∀ (init : BinaryVector n) (vs : List (BinaryVector n)),
      (vs.foldl (fun acc v => vectorXor acc v) init) i =
        vs.foldl (fun acc v => Bool.xor acc (v i)) (init i) := by
    intro init vs
    induction vs generalizing init with
    | nil => rfl
    | cons v rest ih => exact ih (vectorXor init v)
  exact key zeroVector vs

/-- Applying a binary matrix is the fold of its columns, each weighted by the corresponding
entry of the argument. -/
theorem matrixApply_eq_vectorFoldlXor {n : Nat} (J : BinaryMatrix n) (z : BinaryVector n) :
    matrixApply J z =
      vectorFoldlXor ((List.finRange n).map (fun j => fun i => J i j && z j)) := by
  funext i
  rw [vectorFoldlXor_apply, List.foldl_map]
  rfl

/-- The padded coordinate tuple: the tuple on the first `2 * pairCount` coordinates and false
elsewhere. -/
def extendCoordinates {n : Nat} (p : PhaseANF n) (fuel : Nat)
    (y : Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length)
      → Bool) : BinaryVector n :=
  fun j => if h : j.val < 2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length then y ⟨j.val, h⟩ else false

/-- The manuscript's basis matrix: an `n`-by-`n` binary matrix whose first `2 * pairCount`
columns are the basis columns of the polar image and whose remaining columns are zero. -/
noncomputable def supportBasisMatrix {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n) :
    BinaryMatrix n :=
  fun i j => if h : j.val < 2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length then
      supportBasisColumn p fuel hdegree hlen m hsize hb ⟨j.val, h⟩ i
    else false

/-- The `j`-th column of the basis matrix is the `j`-th basis column. -/
theorem supportBasisMatrix_column {n : Nat}
    (p : PhaseANF n) (fuel : Nat)
    (hdegree : phaseWithinDegree 2 p = true)
    (hlen : (recordedCoordinateOrder
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2).length = n)
    (m : Nat)
    (hsize : n = (((polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length +
      (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length) + m))
    (hb : 2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length ≤ n)
    (j : Fin (2 * (polarEliminate (phasePolar p) fuel
      (List.finRange n) identityMatrix).2.2.length)) :
    (fun i => supportBasisMatrix p fuel hdegree hlen m hsize hb i
        ⟨j.val, by have := j.isLt; omega⟩) =
      supportBasisColumn p fuel hdegree hlen m hsize hb j := by
  funext i
  show (if h : (⟨j.val, by have := j.isLt; omega⟩ : Fin n).val <
      2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length then
      supportBasisColumn p fuel hdegree hlen m hsize hb
        ⟨(⟨j.val, by have := j.isLt; omega⟩ : Fin n).val, h⟩ i
    else false) = supportBasisColumn p fuel hdegree hlen m hsize hb j i
  rw [dif_pos j.isLt]

/-- The padded unit tuple: the tuple that is true at one coordinate only. -/
def extendUnit {n : Nat} (p : PhaseANF n) (fuel : Nat)
    (t : Fin (2 * (polarEliminate (phasePolar p) fuel (List.finRange n) identityMatrix).2.2.length)) :
    BinaryVector n :=
  extendCoordinates p fuel (fun j => decide (j = t))

end SectorSimulation
