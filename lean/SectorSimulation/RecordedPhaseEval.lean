import SectorSimulation.SourceInverseEndpoints
namespace SectorSimulation

theorem recordedPairPhase_pairEval {n : Nat} (pairs : List (Fin n × Fin n))
    (x : BinaryVector n) (c : Bool) :
    pairPhaseEval (List.replicate pairs.length (false,false))
      (pairs.map (fun q => (x q.1, x q.2))) c =
      Bool.xor c (evalPhase (recordedPairPhase pairs) x) := by
  rw [recordedPairPhase, evalQuadraticTerms_bitMasks]
  induction pairs generalizing c with
  | nil => cases c <;> rfl
  | cons p rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.map_cons, pairPhaseEval,
      recordedPairTerms, evalQuadraticTerms, evalQuadraticTerm, hyperbolicPhase,
      Bool.false_and, Bool.xor_false]
    rw [ih]
    simp only [recordedPairTerms, Bool.xor_assoc]


end SectorSimulation