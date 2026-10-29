import SectorSimulation.BooleanSource

/-! Finite list shape extraction for represented cubic monomial masks. -/

namespace SectorSimulation

/-- A list of length at most three has one of the four explicit small shapes. -/
theorem list_length_le_three_shape {α : Type} (xs : List α) (h : xs.length ≤ 3) :
    xs = [] ∨ (∃ a, xs = [a]) ∨ (∃ a b, xs = [a, b]) ∨
      (∃ a b c, xs = [a, b, c]) := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons a rest =>
    cases rest with
    | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
    | cons b rest =>
      cases rest with
      | nil => exact Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))
      | cons c rest =>
        cases rest with
        | nil => exact Or.inr (Or.inr (Or.inr ⟨a, b, c, rfl⟩))
        | cons d tail => simp at h

/-- A degree-at-most-three mask has at most three selected indices. -/
theorem cubicMask_selected_shape {n : Nat} (m : Monomial n)
    (h : monomialDegree m ≤ 3) :
    selectedVariables m = [] ∨ (∃ a, selectedVariables m = [a]) ∨
      (∃ a b, selectedVariables m = [a, b]) ∨
      (∃ a b c, selectedVariables m = [a, b, c]) := by
  apply list_length_le_three_shape
  simpa only [← monomialDegree_eq_selectedLength] using h

/-- Evaluation of each extracted small support shape. -/
theorem evalMonomial_selected_nil {n : Nat} (m : Monomial n) (x : BinaryVector n)
    (h : selectedVariables m = []) : evalMonomial m x = true := by
  rw [evalMonomial_selectedVariables, h]
  rfl

theorem evalMonomial_selected_one {n : Nat} (m : Monomial n) (x : BinaryVector n)
    (i : Fin n) (h : selectedVariables m = [i]) : evalMonomial m x = x i := by
  rw [evalMonomial_selectedVariables, h]
  simp

theorem evalMonomial_selected_two {n : Nat} (m : Monomial n) (x : BinaryVector n)
    (i k : Fin n) (h : selectedVariables m = [i, k]) :
    evalMonomial m x = (x i && x k) := by
  rw [evalMonomial_selectedVariables, h]
  simp

theorem evalMonomial_selected_three {n : Nat} (m : Monomial n) (x : BinaryVector n)
    (i k l : Fin n) (h : selectedVariables m = [i, k, l]) :
    evalMonomial m x = (x i && x k && x l) := by
  rw [evalMonomial_selectedVariables, h]
  simp [Bool.and_assoc]

end SectorSimulation
