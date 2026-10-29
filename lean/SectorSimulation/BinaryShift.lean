import SectorSimulation.Derivative

/-! A pointwise binary-vector instance of the derivative bridge. This does
not establish the circuit, polynomial degree or Walsh-support claims. -/

namespace SectorSimulation

def binaryShift {ι : Type} (j x : ι → Bool) : ι → Bool :=
  fun i => Bool.xor (x i) (j i)

theorem binaryShift_involutive {ι : Type} (j x : ι → Bool) :
    binaryShift j (binaryShift j x) = x := by
  funext i
  unfold binaryShift
  cases x i <;> cases j i <;> rfl

theorem binaryDerivative_shift_invariant {ι : Type} (f : (ι → Bool) → Bool)
    (j x : ι → Bool) :
    booleanDerivative f (binaryShift j) (binaryShift j x) =
      booleanDerivative f (binaryShift j) x := by
  exact booleanDerivative_shift_invariant f (binaryShift j) (binaryShift_involutive j) x

end SectorSimulation
