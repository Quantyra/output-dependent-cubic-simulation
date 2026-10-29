import SectorSimulation.SourceCanonicalCharacter
import SectorSimulation.BinaryTransposeCharacter

namespace SectorSimulation

theorem sourceWalshSum_transposedCanonical {k m : Nat} (p : PhaseANF ((k+k)+m))
    (l : BinaryVector ((k+k)+m)) (J : BinaryMatrix ((k+k)+m))
    (ops : List (RowOperation ((k+k)+m))) (hJ : gaussianRowProgram J = some ops)
    (ps : List (Bool × Bool)) (bs : List Bool) (c : Bool) (hp : ps.length = k) (hb : bs.length = m)
    (hphase : ∀ y, evalPhase p (matrixApply J y) = evalPhase (canonicalPhaseANF k m ps bs c) y) :
    sourceWalshSum p l =
      if (radicalCoefficientsXor bs (vectorAssignment (canonicalRadical (matrixApply (transposeBinaryMatrix J) l)))).any id then 0
      else (2 : Int)^(m+k) * integerWalshSign
        (Bool.xor c (hyperbolicSignature (pairCoefficientsXor ps
          (vectorPairAssignment (canonicalLeft (matrixApply (transposeBinaryMatrix J) l))
            (canonicalRight (matrixApply (transposeBinaryMatrix J) l)))))) := by
  exact sourceWalshSum_knownCanonical p l (matrixApply (transposeBinaryMatrix J) l) J ops hJ ps bs c hp hb hphase
    (binaryTranspose_character J l)


end SectorSimulation
