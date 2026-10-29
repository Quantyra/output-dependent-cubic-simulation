import SectorSimulation.CanonicalCharacterShift

namespace SectorSimulation

theorem pairCoefficientsXor_length (ps qs : List (Bool × Bool)) (h : ps.length = qs.length) :
    (pairCoefficientsXor ps qs).length = ps.length := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp_all [pairCoefficientsXor]
  | cons p ps ih =>
    cases qs with
    | nil => simp at h
    | cons q qs =>
      rcases p with ⟨a,b⟩
      rcases q with ⟨d,e⟩
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp [pairCoefficientsXor, ih qs h]

theorem radicalCoefficientsXor_length (bs ds : List Bool) (h : bs.length = ds.length) :
    (radicalCoefficientsXor bs ds).length = bs.length := by
  induction bs generalizing ds with
  | nil => cases ds <;> simp_all [radicalCoefficientsXor]
  | cons b bs ih =>
    cases ds with
    | nil => simp at h
    | cons d ds =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp [radicalCoefficientsXor, ih ds h]

def canonicalLinearCharacter {k m : Nat} (qs : List (Bool × Bool)) (ds : List Bool)
    (x : BinaryVector ((k+k)+m)) : Bool :=
  Bool.xor (pairLinearEval qs (canonicalAssignment x).2) (radicalLinearEval ds (canonicalAssignment x).1)

theorem canonicalPhase_shift {k m : Nat} (ps qs : List (Bool × Bool)) (bs ds : List Bool)
    (c : Bool) (x : BinaryVector ((k+k)+m)) (hp : ps.length = qs.length) (hr : bs.length = ds.length) :
    Bool.xor (canonicalPhaseOnVector ps bs c x) (canonicalLinearCharacter qs ds x) =
      canonicalPhaseOnVector (pairCoefficientsXor ps qs) (radicalCoefficientsXor bs ds) c x := by
  unfold canonicalPhaseOnVector canonicalLinearCharacter
  have hpair := pairPhaseEval_shift ps qs (canonicalAssignment x).2 false hp
  have hrad := radicalPhaseEval_shift bs ds (canonicalAssignment x).1 c hr
  rw [pairPhaseEval_offset ps (canonicalAssignment x).2,
    pairPhaseEval_offset (pairCoefficientsXor ps qs) (canonicalAssignment x).2]
  rw [← hpair, ← hrad]
  cases radicalPhaseEval bs (canonicalAssignment x).1 c <;>
    cases radicalLinearEval ds (canonicalAssignment x).1 <;>
    cases pairPhaseEval ps (canonicalAssignment x).2 false <;>
    cases pairLinearEval qs (canonicalAssignment x).2 <;>
    simp_all

def canonicalCharacterWalshSum {k m : Nat} (ps qs : List (Bool × Bool))
    (bs ds : List Bool) (c : Bool) : Int :=
  ((binaryBasis ((k+k)+m)).map (fun x => integerWalshSign
    (Bool.xor (canonicalPhaseOnVector ps bs c x) (canonicalLinearCharacter qs ds x)))).sum

theorem canonicalCharacterWalshSum_closed {k m : Nat} (ps qs : List (Bool × Bool))
    (bs ds : List Bool) (c : Bool) (hp : ps.length = k) (hq : qs.length = k)
    (hb : bs.length = m) (hd : ds.length = m) :
    canonicalCharacterWalshSum (k := k) (m := m) ps qs bs ds c =
      if (radicalCoefficientsXor bs ds).any id then 0 else (2 : Int)^(m+k) *
        integerWalshSign (Bool.xor c (hyperbolicSignature (pairCoefficientsXor ps qs))) := by
  have hpq : ps.length = qs.length := hp.trans hq.symm
  have hbd : bs.length = ds.length := hb.trans hd.symm
  have hpair : (pairCoefficientsXor ps qs).length = k := (pairCoefficientsXor_length ps qs hpq).trans hp
  have hrad : (radicalCoefficientsXor bs ds).length = m := (radicalCoefficientsXor_length bs ds hbd).trans hb
  have he : canonicalCharacterWalshSum (k := k) (m := m) ps qs bs ds c =
      canonicalVectorWalshSum (k := k) (m := m) (pairCoefficientsXor ps qs) (radicalCoefficientsXor bs ds) c := by
    unfold canonicalCharacterWalshSum canonicalVectorWalshSum
    simp only [canonicalPhase_shift ps qs bs ds c _ hpq hbd]
  rw [he, canonicalVectorWalshSum_closed _ _ _ hpair hrad]


end SectorSimulation
