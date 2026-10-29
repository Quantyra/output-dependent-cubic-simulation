import SectorSimulation.CanonicalCharacterDot
import SectorSimulation.SourceWalshReindex

namespace SectorSimulation

theorem sourceWalshSum_knownCanonical {k m : Nat} (p : PhaseANF ((k+k)+m))
    (l t : BinaryVector ((k+k)+m)) (J : BinaryMatrix ((k+k)+m))
    (ops : List (RowOperation ((k+k)+m))) (hJ : gaussianRowProgram J = some ops)
    (ps : List (Bool × Bool)) (bs : List Bool) (c : Bool) (hp : ps.length = k) (hb : bs.length = m)
    (hphase : ∀ y, evalPhase p (matrixApply J y) = evalPhase (canonicalPhaseANF k m ps bs c) y)
    (hchar : ∀ y, walshWireParity (List.finRange ((k+k)+m)) l (matrixApply J y) =
      walshWireParity (List.finRange ((k+k)+m)) t y) :
    sourceWalshSum p l =
      if (radicalCoefficientsXor bs (vectorAssignment (canonicalRadical t))).any id then 0
      else (2 : Int)^(m+k) * integerWalshSign
        (Bool.xor c (hyperbolicSignature (pairCoefficientsXor ps
          (vectorPairAssignment (canonicalLeft t) (canonicalRight t))))) := by
  rw [sourceWalshSum_reindex p l J ops hJ]
  have he : ((binaryBasis ((k+k)+m)).map (fun y => integerWalshSign
      (Bool.xor (evalPhase p (matrixApply J y))
        (walshWireParity (List.finRange ((k+k)+m)) l (matrixApply J y))))).sum =
      canonicalDotWalshSum ps bs c t := by
    unfold canonicalDotWalshSum
    simp only [hphase, hchar]
  rw [he, canonicalDotWalshSum_closed ps bs c t hp hb]


end SectorSimulation
