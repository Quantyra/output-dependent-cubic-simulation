import Std

/-!
A small algebraic bridge toward Proposition 2.2 of the published paper.
This establishes only shift invariance of a Boolean derivative when the
shift is involutive. It does not formalize the circuit, Walsh transform,
sector normalization, discovery, estimator, or any complexity claim.
-/

namespace SectorSimulation

def booleanDerivative {α : Type} (f : α → Bool) (shift : α → α) (x : α) : Bool :=
  Bool.xor (f x) (f (shift x))

theorem booleanDerivative_shift_invariant {α : Type} (f : α → Bool)
    (shift : α → α) (involutive : ∀ x, shift (shift x) = x) (x : α) :
    booleanDerivative f shift (shift x) = booleanDerivative f shift x := by
  unfold booleanDerivative
  rw [involutive]
  cases f x <;> cases f (shift x) <;> rfl

end SectorSimulation
