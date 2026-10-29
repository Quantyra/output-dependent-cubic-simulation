import SectorSimulation.QuadraticTerms

/-!
Construct a quadratic term list for the derivative of one bit-mask monomial
of degree at most three. Translation of the term language to the source's
bit-mask ANF and lifting over a whole cubic phase remain separate obligations.
-/

namespace SectorSimulation

/-- Return no term list when the selected support has more than three entries. -/
def cubicMaskDerivativeTerms {n : Nat} (m : Monomial n) (j : BinaryVector n) :
    Option (List (QuadraticTerm n)) :=
  match selectedVariables m with
  | [] => some []
  | [i] => some (linearDerivativeTerms i j)
  | [i, k] => some (quadraticDerivativeTerms i k j)
  | [i, k, l] => some (cubicDerivativeTerms i k l j)
  | _ => none

/-- Every degree-at-most-three mask has a constructed, semantically correct
quadratic term list for its Boolean derivative. -/
theorem cubicMaskDerivativeTerms_correct {n : Nat} (m : Monomial n)
    (j : BinaryVector n) (hdegree : monomialDegree m ≤ 3) :
    ∃ terms, cubicMaskDerivativeTerms m j = some terms ∧
      ∀ x, evalQuadraticTerms terms x =
        booleanDerivative (evalMonomial m) (binaryShift j) x := by
  rcases cubicMask_selected_shape m hdegree with h0 | ⟨i, h1⟩ |
    ⟨i, k, h2⟩ | ⟨i, k, l, h3⟩
  · refine ⟨[], ?_, ?_⟩
    · simp [cubicMaskDerivativeTerms, h0]
    · intro x
      have heval : evalMonomial m = fun _ => true := by
        funext v
        exact evalMonomial_selected_nil m v h0
      rw [heval]
      rfl
  · refine ⟨linearDerivativeTerms i j, ?_, ?_⟩
    · simp [cubicMaskDerivativeTerms, h1]
    · intro x
      have heval : evalMonomial m = fun v => v i := by
        funext v
        exact evalMonomial_selected_one m v i h1
      rw [heval]
      exact evalLinearDerivativeTerms i j x
  · refine ⟨quadraticDerivativeTerms i k j, ?_, ?_⟩
    · simp [cubicMaskDerivativeTerms, h2]
    · intro x
      have heval : evalMonomial m = fun v => v i && v k := by
        funext v
        exact evalMonomial_selected_two m v i k h2
      rw [heval]
      exact evalQuadraticDerivativeTerms i k j x
  · refine ⟨cubicDerivativeTerms i k l j, ?_, ?_⟩
    · simp [cubicMaskDerivativeTerms, h3]
    · intro x
      have heval : evalMonomial m = fun v => v i && v k && v l := by
        funext v
        exact evalMonomial_selected_three m v i k l h3
      rw [heval]
      exact evalCubicDerivativeTerms i k l j x

end SectorSimulation
