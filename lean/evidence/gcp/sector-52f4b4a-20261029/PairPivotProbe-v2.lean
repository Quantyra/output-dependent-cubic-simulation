import SectorSimulation.PairColumnsPrior
namespace SectorSimulation

def findPolarPair {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (indices : List (Fin n)) : Option (Fin n × Fin n) :=
  (indices.product indices).find? fun p =>
    decide (p.1 ∈ indices) && decide (p.2 ∈ indices) && B (matrixColumn J p.1) (matrixColumn J p.2)

theorem findPolarPair_sound {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (indices : List (Fin n)) (u v : Fin n)
    (h : findPolarPair B J indices = some (u,v)) :
    u ∈ indices ∧ v ∈ indices ∧ B (matrixColumn J u) (matrixColumn J v) = true := by
  have hp := List.find?_some (p := fun p : Fin n × Fin n =>
    decide (p.1 ∈ indices) && decide (p.2 ∈ indices) && B (matrixColumn J p.1) (matrixColumn J p.2)) h
  simpa [and_assoc] using hp

theorem findPolarPair_none {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (indices : List (Fin n))
    (h : findPolarPair B J indices = none) :
    ∀ u ∈ indices, ∀ v ∈ indices, B (matrixColumn J u) (matrixColumn J v) = false := by
  have hn := List.find?_eq_none.mp h
  intro u hu v hv
  have hp := hn (u,v) (by simp [hu,hv])
  simpa [hu,hv] using hp

theorem findPolarPair_distinct {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (indices : List (Fin n)) (u v : Fin n)
    (halt : ∀ x, B x x = false) (h : findPolarPair B J indices = some (u,v)) : u ≠ v := by
  intro he
  subst v
  have hp := (findPolarPair_sound B J indices u u h).2.2
  rw [halt] at hp
  contradiction
end SectorSimulation
#print axioms SectorSimulation.findPolarPair_sound
#print axioms SectorSimulation.findPolarPair_none
#print axioms SectorSimulation.findPolarPair_distinct
