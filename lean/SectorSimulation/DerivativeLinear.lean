import SectorSimulation.Derivative

/-! Boolean differentiation is additive. This algebraic helper supports the
ANF degree-drop argument but does not itself prove the degree bound. -/

namespace SectorSimulation

theorem booleanDerivative_xor {α : Type} (f g : α → Bool)
    (shift : α → α) (x : α) :
    booleanDerivative (fun y => Bool.xor (f y) (g y)) shift x =
      Bool.xor (booleanDerivative f shift x) (booleanDerivative g shift x) := by
  cases hf : f x <;> cases hg : g x <;>
    cases hfs : f (shift x) <;> cases hgs : g (shift x) <;>
    simp [booleanDerivative, hf, hg, hfs, hgs]

end SectorSimulation
