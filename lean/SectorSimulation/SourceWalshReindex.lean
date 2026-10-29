import SectorSimulation.CanonicalSourceANF
import SectorSimulation.HadamardMatrixSum

namespace SectorSimulation

def sourceWalshSum {n : Nat} (p : PhaseANF n) (l : BinaryVector n) : Int :=
  ((binaryBasis n).map (fun x => integerWalshSign (Bool.xor (evalPhase p x)
    (walshWireParity (List.finRange n) l x)))).sum

theorem sourceWalshSum_reindex {n : Nat} (p : PhaseANF n) (l : BinaryVector n)
    (J : BinaryMatrix n) (ops : List (RowOperation n)) (hp : gaussianRowProgram J = some ops) :
    sourceWalshSum p l = ((binaryBasis n).map (fun y => integerWalshSign
      (Bool.xor (evalPhase p (matrixApply J y))
        (walshWireParity (List.finRange n) l (matrixApply J y))))).sum := by
  have h := integerSum_perm _ _ (matrixApply_basis_perm J ops hp).symm
    (fun x => integerWalshSign (Bool.xor (evalPhase p x)
      (walshWireParity (List.finRange n) l x)))
  simpa [sourceWalshSum, List.map_map, Function.comp_def] using h

theorem sourceWalshSum_canonicalized {k m : Nat} (p : PhaseANF ((k+k)+m))
    (l : BinaryVector ((k+k)+m)) (J : BinaryMatrix ((k+k)+m))
    (ops : List (RowOperation ((k+k)+m))) (hJ : gaussianRowProgram J = some ops)
    (ps : List (Bool × Bool)) (rs : List Bool) (c : Bool)
    (hp : ps.length = k) (hr : rs.length = m)
    (hphase : ∀ y, Bool.xor (evalPhase p (matrixApply J y))
      (walshWireParity (List.finRange ((k+k)+m)) l (matrixApply J y)) =
        evalPhase (canonicalPhaseANF k m ps rs c) y) :
    sourceWalshSum p l = if rs.any id then 0 else (2 : Int)^(m+k) *
      integerWalshSign (Bool.xor c (hyperbolicSignature ps)) := by
  rw [sourceWalshSum_reindex p l J ops hJ]
  have he : ((binaryBasis ((k+k)+m)).map (fun y => integerWalshSign
      (Bool.xor (evalPhase p (matrixApply J y))
        (walshWireParity (List.finRange ((k+k)+m)) l (matrixApply J y))))).sum =
      anfWalshZeroSum (canonicalPhaseANF k m ps rs c) := by
    simp only [hphase, anfWalshZeroSum]
  rw [he, canonicalPhaseANF_walshSum ps rs c hp hr]


end SectorSimulation
