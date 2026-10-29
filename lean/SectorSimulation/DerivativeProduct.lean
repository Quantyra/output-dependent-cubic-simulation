import SectorSimulation.BinaryShift
import SectorSimulation.DerivativeLinear

/-! Product and variable rules for finite Boolean differences. These are
bridges toward the ANF degree theorem, not the degree theorem itself. -/

namespace SectorSimulation

theorem booleanDerivative_const {α : Type} (b : Bool) (shift : α → α) (x : α) :
    booleanDerivative (fun _ => b) shift x = false := by
  cases b <;> rfl

/-- Finite-difference product rule over F2, including the cross term. -/
theorem booleanDerivative_and {α : Type} (f g : α → Bool)
    (shift : α → α) (x : α) :
    booleanDerivative (fun y => f y && g y) shift x =
      Bool.xor
        (Bool.xor (booleanDerivative f shift x && g x)
          (f x && booleanDerivative g shift x))
        (booleanDerivative f shift x && booleanDerivative g shift x) := by
  cases hf : f x <;> cases hg : g x <;>
    cases hfs : f (shift x) <;> cases hgs : g (shift x) <;>
    simp [booleanDerivative, hf, hg, hfs, hgs]

/-- Differentiating one binary coordinate in direction `j` returns `j i`. -/
theorem binaryVariable_derivative {ι : Type} (j x : ι → Bool) (i : ι) :
    booleanDerivative (fun v => v i) (binaryShift j) x = j i := by
  cases hx : x i <;> cases hj : j i <;> simp [booleanDerivative, binaryShift, hx, hj]

end SectorSimulation
