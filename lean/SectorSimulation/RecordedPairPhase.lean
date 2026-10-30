import SectorSimulation.SourcePolarChange
namespace SectorSimulation

def recordedPairTerms {n : Nat} (pairs : List (Fin n × Fin n)) : List (QuadraticTerm n) :=
  pairs.map (fun p => QuadraticTerm.product p.1 p.2)

def recordedPairPhase {n : Nat} (pairs : List (Fin n × Fin n)) : PhaseANF n :=
  quadraticTermsToANF (recordedPairTerms pairs)

def recordedPairPolar {n : Nat} : List (Fin n × Fin n) → BinaryVector n → BinaryVector n → Bool
  | [], _, _ => false
  | p :: ps, u, v => Bool.xor (Bool.xor (u p.1 && v p.2) (u p.2 && v p.1))
      (recordedPairPolar ps u v)

theorem recordedPairPhase_degree {n : Nat} (pairs : List (Fin n × Fin n)) :
    phaseWithinDegree 2 (recordedPairPhase pairs) = true := by
  exact quadraticTermsToANF_degree _

theorem recordedPairPhase_polar {n : Nat} (pairs : List (Fin n × Fin n))
    (u v : BinaryVector n) :
    phasePolar (recordedPairPhase pairs) u v = recordedPairPolar pairs u v := by
  rw [recordedPairPhase, ← termsPolar_correct]
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    simp only [recordedPairTerms, List.map_cons, termsPolar, termPolar, recordedPairPolar] at *
    rw [ih]
end SectorSimulation
