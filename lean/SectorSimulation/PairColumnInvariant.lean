import SectorSimulation.PairColumnList
namespace SectorSimulation

theorem clearPairColumns_other {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v j : Fin n) (ts : List (Fin n)) (J : BinaryMatrix n) (hj : j ∉ ts) :
    matrixColumn (clearPairColumns B u v ts J).1 j = matrixColumn J j := by
  induction ts generalizing J with
  | nil => rfl
  | cons t ts ih =>
    have h : j ≠ t ∧ j ∉ ts := by simpa using hj
    simp only [clearPairColumns]
    rw [ih _ h.2]
    exact clearPairColumn_other B J t u v j h.1

end SectorSimulation
