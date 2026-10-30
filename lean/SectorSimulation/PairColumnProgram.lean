import SectorSimulation.PairColumnBridge
namespace SectorSimulation

def pairColumnOps {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (t u v : Fin n) : List (Fin n × Fin n) :=
  (if B (matrixColumn J t) (matrixColumn J v) then [(t,u)] else []) ++
  (if B (matrixColumn J t) (matrixColumn J u) then [(t,v)] else [])

theorem pairColumnOps_apply {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (t u v : Fin n) :
    runColumnAdds (pairColumnOps B J t u v) J = clearPairColumn B J t u v := by
  cases h1 : B (matrixColumn J t) (matrixColumn J v) <;>
    cases h2 : B (matrixColumn J t) (matrixColumn J u) <;>
    simp [pairColumnOps, runColumnAdds, clearPairColumn, h1, h2]

theorem pairColumnOps_reverse {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (J : BinaryMatrix n) (t u v : Fin n) :
    runColumnAdds (pairColumnOps B J t u v).reverse (clearPairColumn B J t u v) = J := by
  rw [← pairColumnOps_apply]
  exact runColumnAdds_reverse_cancels _ _

end SectorSimulation
