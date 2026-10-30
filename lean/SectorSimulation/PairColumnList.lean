import SectorSimulation.PairColumnProgram
namespace SectorSimulation

def clearPairColumns {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v : Fin n) : List (Fin n) → BinaryMatrix n → BinaryMatrix n × List (Fin n × Fin n)
  | [], J => (J, [])
  | t :: ts, J =>
    let ops := pairColumnOps B J t u v
    let result := clearPairColumns B u v ts (clearPairColumn B J t u v)
    (result.1, ops ++ result.2)

theorem clearPairColumns_program {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v : Fin n) (ts : List (Fin n)) (J : BinaryMatrix n) :
    runColumnAdds (clearPairColumns B u v ts J).2 J = (clearPairColumns B u v ts J).1 := by
  induction ts generalizing J with
  | nil => rfl
  | cons t ts ih =>
    simp only [clearPairColumns]
    simp only [runColumnAdds, List.foldl_append]
    change runColumnAdds (clearPairColumns B u v ts (clearPairColumn B J t u v)).2
      (runColumnAdds (pairColumnOps B J t u v) J) = _
    rw [pairColumnOps_apply]
    exact ih _

theorem clearPairColumns_reverse {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (u v : Fin n) (ts : List (Fin n)) (J : BinaryMatrix n) :
    runColumnAdds (clearPairColumns B u v ts J).2.reverse
      (clearPairColumns B u v ts J).1 = J := by
  rw [← clearPairColumns_program]
  exact runColumnAdds_reverse_cancels _ _

end SectorSimulation
