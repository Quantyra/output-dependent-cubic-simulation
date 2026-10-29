import SectorSimulation.CanonicalCharacterParity

namespace SectorSimulation

theorem canonicalLinearCharacter_dot {k m : Nat} (l x : BinaryVector ((k+k)+m)) :
    canonicalLinearCharacter (vectorPairAssignment (canonicalLeft l) (canonicalRight l))
      (vectorAssignment (canonicalRadical l)) x =
        walshWireParity (List.finRange ((k+k)+m)) l x := by
  unfold canonicalLinearCharacter canonicalAssignment vectorPairAssignment vectorAssignment
  rw [pairLinearEval_map, radicalLinearEval_map]
  rw [finRange_split (k+k) m, walshWireParity_append, walshWireParity_map]
  rw [finRange_split k k, walshWireParity_append, walshWireParity_map, walshWireParity_map, walshWireParity_map]
  rfl

def canonicalDotWalshSum {k m : Nat} (ps : List (Bool × Bool)) (bs : List Bool)
    (c : Bool) (l : BinaryVector ((k+k)+m)) : Int :=
  ((binaryBasis ((k+k)+m)).map (fun x => integerWalshSign
    (Bool.xor (evalPhase (canonicalPhaseANF k m ps bs c) x)
      (walshWireParity (List.finRange ((k+k)+m)) l x)))).sum

theorem canonicalDotWalshSum_closed {k m : Nat} (ps : List (Bool × Bool)) (bs : List Bool)
    (c : Bool) (l : BinaryVector ((k+k)+m)) (hp : ps.length = k) (hb : bs.length = m) :
    canonicalDotWalshSum ps bs c l =
      if (radicalCoefficientsXor bs (vectorAssignment (canonicalRadical l))).any id then 0
      else (2 : Int)^(m+k) * integerWalshSign
        (Bool.xor c (hyperbolicSignature (pairCoefficientsXor ps
          (vectorPairAssignment (canonicalLeft l) (canonicalRight l))))) := by
  let qs := vectorPairAssignment (canonicalLeft l) (canonicalRight l)
  let ds := vectorAssignment (canonicalRadical l)
  have he : canonicalDotWalshSum ps bs c l = canonicalCharacterWalshSum (k := k) (m := m) ps qs bs ds c := by
    unfold canonicalDotWalshSum canonicalCharacterWalshSum
    simp only [canonicalPhaseANF_correct ps bs c hp hb, ← canonicalLinearCharacter_dot l]
    rfl
  rw [he, canonicalCharacterWalshSum_closed ps qs bs ds c hp (vectorPairAssignment_length _ _) hb (vectorAssignment_length _)]


end SectorSimulation
