import SectorSimulation.BinaryTransposeCharacter
import SectorSimulation.MatrixRowOperations
namespace SectorSimulation

def columnAdd {n : Nat} (J : BinaryMatrix n) (target source : Fin n) : BinaryMatrix n :=
  fun i j => if j = target then Bool.xor (J i target) (J i source) else J i j

theorem booleanListSum_singleton {n : Nat} (xs : List (Fin n)) (k : Fin n)
    (f : Fin n → Bool) (hn : xs.Nodup) :
    booleanListSum xs (fun j => decide (j = k) && f j) = if k ∈ xs then f k else false := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have hr := List.nodup_cons.mp hn
    by_cases h : a = k
    · subst a
      change Bool.xor (decide (k = k) && f k)
        (booleanListSum rest (fun j => decide (j = k) && f j)) = _
      rw [ih hr.2]
      simp [hr.1]
    · change Bool.xor (decide (a = k) && f a)
        (booleanListSum rest (fun j => decide (j = k) && f j)) = _
      rw [ih hr.2]
      simp [h, Ne.symm h]

theorem columnAdd_action {n : Nat} (J : BinaryMatrix n) (target source : Fin n)
    (x : BinaryVector n) :
    matrixApply (columnAdd J target source) x = matrixApply J (vectorAddRow x source target) := by
  funext i
  simp only [matrixApply, xorFoldl_as_sum, Bool.false_xor]
  have hl : (fun j => columnAdd J target source i j && x j) =
      (fun j => Bool.xor (J i j && x j) (decide (j = target) && (J i source && x j))) := by
    funext j
    by_cases h : j = target
    · subst j
      simp only [columnAdd, if_pos rfl, decide_true, Bool.true_and]
      cases J i target <;> cases J i source <;> cases x target <;> rfl
    · simp [columnAdd, h]
  have hr : (fun j => J i j && vectorAddRow x source target j) =
      (fun j => Bool.xor (J i j && x j) (decide (j = source) && (J i j && x target))) := by
    funext j
    by_cases h : j = source
    · subst j
      simp only [vectorAddRow, if_pos rfl, decide_true, Bool.true_and]
      cases J i source <;> cases x source <;> cases x target <;> rfl
    · simp [vectorAddRow, h]
  rw [hl, hr, booleanListSum_xor, booleanListSum_xor]
  rw [booleanListSum_singleton _ target _ (List.nodup_finRange n),
    booleanListSum_singleton _ source _ (List.nodup_finRange n)]
  simp [Bool.and_comm]

end SectorSimulation
