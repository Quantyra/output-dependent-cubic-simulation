import SectorSimulation.CanonicalVectorWalsh
import SectorSimulation.CubicDerivativeANF
namespace SectorSimulation

def canonicalPairTerms {n : Nat} : List (Bool × Bool) → List (Fin n × Fin n) → List (QuadraticTerm n)
  | (a,b)::ps, (u,v)::ws =>
      [QuadraticTerm.product u v] ++ conditionalQuadraticTerm a (.linear u) ++
        conditionalQuadraticTerm b (.linear v) ++ canonicalPairTerms ps ws
  | _, _ => []

theorem canonicalPairTerms_correct {n : Nat} (ps : List (Bool × Bool))
    (ws : List (Fin n × Fin n)) (h : ps.length = ws.length) (x : BinaryVector n) (c : Bool) :
    pairPhaseEval ps (ws.map (fun uv => (x uv.1, x uv.2))) c =
      Bool.xor c (evalQuadraticTerms (canonicalPairTerms ps ws) x) := by
  induction ps generalizing ws c with
  | nil =>
    cases ws with
    | nil => cases c <;> rfl
    | cons w rest => simp at h
  | cons p rest ih =>
    cases ws with
    | nil => simp at h
    | cons w tail =>
      rcases p with ⟨a,b⟩
      rcases w with ⟨u,v⟩
      have ht : rest.length = tail.length := by simpa using h
      simp only [List.map_cons, pairPhaseEval, canonicalPairTerms, evalQuadraticTerms_append,
        evalQuadraticTerms, evalQuadraticTerm, Bool.xor_false, evalConditionalQuadraticTerm]
      rw [ih tail ht]
      cases c <;> cases a <;> cases b <;> cases x u <;> cases x v <;>
        cases evalQuadraticTerms (canonicalPairTerms rest tail) x <;> rfl


def canonicalRadicalTerms {n : Nat} : List Bool → List (Fin n) → List (QuadraticTerm n)
  | b::bs, w::ws => conditionalQuadraticTerm b (.linear w) ++ canonicalRadicalTerms bs ws
  | _, _ => []

theorem canonicalRadicalTerms_correct {n : Nat} (bs : List Bool) (ws : List (Fin n))
    (h : bs.length = ws.length) (x : BinaryVector n) (c : Bool) :
    radicalPhaseEval bs (ws.map x) c = Bool.xor c (evalQuadraticTerms (canonicalRadicalTerms bs ws) x) := by
  induction bs generalizing ws c with
  | nil =>
    cases ws with
    | nil => cases c <;> rfl
    | cons w rest => simp at h
  | cons b rest ih =>
    cases ws with
    | nil => simp at h
    | cons w tail =>
      have ht : rest.length = tail.length := by simpa using h
      simp only [List.map_cons, radicalPhaseEval, canonicalRadicalTerms, evalQuadraticTerms_append,
        evalConditionalQuadraticTerm, evalQuadraticTerm]
      rw [ih tail ht]
      cases c <;> cases b <;> cases x w <;> cases evalQuadraticTerms (canonicalRadicalTerms rest tail) x <;> rfl

def canonicalPairWires (k m : Nat) : List (Fin ((k+k)+m) × Fin ((k+k)+m)) :=
  (List.finRange k).map (fun i => ((i.castAdd k).castAdd m, (Fin.natAdd k i).castAdd m))

def canonicalRadicalWires (k m : Nat) : List (Fin ((k+k)+m)) :=
  (List.finRange m).map (Fin.natAdd (k+k))

def canonicalPhaseTerms (k m : Nat) (ps : List (Bool × Bool)) (rs : List Bool) (c : Bool) :
    List (QuadraticTerm ((k+k)+m)) :=
  conditionalQuadraticTerm c .constant ++ canonicalPairTerms ps (canonicalPairWires k m) ++
    canonicalRadicalTerms rs (canonicalRadicalWires k m)

theorem canonicalPhaseTerms_correct {k m : Nat} (ps : List (Bool × Bool)) (rs : List Bool)
    (c : Bool) (hp : ps.length = k) (hr : rs.length = m) (x : BinaryVector ((k+k)+m)) :
    canonicalPhaseOnVector ps rs c x = evalQuadraticTerms (canonicalPhaseTerms k m ps rs c) x := by
  have hpair : ps.length = (canonicalPairWires k m).length := by simp [canonicalPairWires, hp]
  have hrad : rs.length = (canonicalRadicalWires k m).length := by simp [canonicalRadicalWires, hr]
  have hpv : (canonicalPairWires k m).map (fun uv => (x uv.1, x uv.2)) =
      (canonicalAssignment x).2 := by
    simp [canonicalPairWires, canonicalAssignment, vectorPairAssignment, canonicalLeft, canonicalRight,
      List.map_map, Function.comp_def]
  have hrv : (canonicalRadicalWires k m).map x = (canonicalAssignment x).1 := by
    simp [canonicalRadicalWires, canonicalAssignment, vectorAssignment, canonicalRadical,
      List.map_map, Function.comp_def]
  have hp' := canonicalPairTerms_correct ps (canonicalPairWires k m) hpair x
    (radicalPhaseEval rs (canonicalAssignment x).1 c)
  have hr' := canonicalRadicalTerms_correct rs (canonicalRadicalWires k m) hrad x c
  rw [hpv] at hp'
  rw [hrv] at hr'
  unfold canonicalPhaseOnVector
  rw [hp', hr']
  simp only [canonicalPhaseTerms, evalQuadraticTerms_append,
    evalConditionalQuadraticTerm, evalQuadraticTerm, Bool.and_true]
  cases c <;> cases evalQuadraticTerms (canonicalPairTerms ps (canonicalPairWires k m)) x <;>
    cases evalQuadraticTerms (canonicalRadicalTerms rs (canonicalRadicalWires k m)) x <;> rfl

def canonicalPhaseANF (k m : Nat) (ps : List (Bool × Bool)) (rs : List Bool) (c : Bool) :
    PhaseANF ((k+k)+m) := quadraticTermsToANF (canonicalPhaseTerms k m ps rs c)

theorem canonicalPhaseANF_correct {k m : Nat} (ps : List (Bool × Bool)) (rs : List Bool)
    (c : Bool) (hp : ps.length = k) (hr : rs.length = m) (x : BinaryVector ((k+k)+m)) :
    evalPhase (canonicalPhaseANF k m ps rs c) x = canonicalPhaseOnVector ps rs c x := by
  rw [canonicalPhaseANF, evalQuadraticTerms_bitMasks]
  exact (canonicalPhaseTerms_correct ps rs c hp hr x).symm


theorem canonicalPhaseANF_degree (k m : Nat) (ps : List (Bool × Bool)) (rs : List Bool) (c : Bool) :
    phaseWithinDegree 2 (canonicalPhaseANF k m ps rs c) = true := by
  exact quadraticTermsToANF_degree _

def anfWalshZeroSum {n : Nat} (p : PhaseANF n) : Int :=
  ((binaryBasis n).map (fun x => integerWalshSign (evalPhase p x))).sum

theorem canonicalPhaseANF_walshSum {k m : Nat} (ps : List (Bool × Bool)) (rs : List Bool)
    (c : Bool) (hp : ps.length = k) (hr : rs.length = m) :
    anfWalshZeroSum (canonicalPhaseANF k m ps rs c) =
      if rs.any id then 0 else (2 : Int)^(m+k) *
        integerWalshSign (Bool.xor c (hyperbolicSignature ps)) := by
  have he : anfWalshZeroSum (canonicalPhaseANF k m ps rs c) =
      canonicalVectorWalshSum (k := k) (m := m) ps rs c := by
    unfold anfWalshZeroSum canonicalVectorWalshSum
    simp only [canonicalPhaseANF_correct ps rs c hp hr]
  rw [he, canonicalVectorWalshSum_closed ps rs c hp hr]

end SectorSimulation
