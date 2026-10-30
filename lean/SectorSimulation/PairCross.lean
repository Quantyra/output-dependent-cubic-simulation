import SectorSimulation.PairUnit
namespace SectorSimulation

theorem recordedPairPolar_unit_unrelated {n : Nat} (pairs : List (Fin n × Fin n))
    (i j : Fin n)
    (h : ∀ p ∈ pairs, ¬ ((i = p.1 ∧ j = p.2) ∨ (i = p.2 ∧ j = p.1))) :
    recordedPairPolar pairs (coordinateUnit i) (coordinateUnit j) = false := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    have hp := h p (by simp)
    have ht : ∀ q ∈ ps, ¬ ((i = q.1 ∧ j = q.2) ∨ (i = q.2 ∧ j = q.1)) := by
      intro q hq; exact h q (by simp [hq])
    have htzero := ih ht
    simp only [recordedPairPolar, coordinateUnit, htzero, Bool.xor_false]
    by_cases h1 : p.1 = i <;> by_cases h2 : p.2 = j <;>
      by_cases h3 : p.2 = i <;> by_cases h4 : p.1 = j <;> simp_all

theorem recordedPairPolar_unit_diagonal {n : Nat} (pairs : List (Fin n × Fin n))
    (i : Fin n) : recordedPairPolar pairs (coordinateUnit i) (coordinateUnit i) = false := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => simp [recordedPairPolar, ih, Bool.and_comm]
end SectorSimulation
