import SectorSimulation.CanonicalSourceANF

namespace SectorSimulation

def pairLinearEval : List (Bool × Bool) → List (Bool × Bool) → Bool
  | (a,b)::ps, (u,v)::xs => Bool.xor (Bool.xor (a && u) (b && v)) (pairLinearEval ps xs)
  | _, _ => false

def radicalLinearEval : List Bool → List Bool → Bool
  | b::bs, x::xs => Bool.xor (b && x) (radicalLinearEval bs xs)
  | _, _ => false

def pairCoefficientsXor : List (Bool × Bool) → List (Bool × Bool) → List (Bool × Bool)
  | (a,b)::ps, (d,e)::qs => (Bool.xor a d, Bool.xor b e)::pairCoefficientsXor ps qs
  | _, _ => []

def radicalCoefficientsXor : List Bool → List Bool → List Bool
  | b::bs, d::ds => Bool.xor b d :: radicalCoefficientsXor bs ds
  | _, _ => []


theorem radicalPhaseEval_offset (bs xs : List Bool) (c : Bool) :
    radicalPhaseEval bs xs c = Bool.xor c (radicalPhaseEval bs xs false) := by
  induction bs generalizing xs c with
  | nil => cases c <;> rfl
  | cons b bs ih =>
    cases xs with
    | nil => cases c <;> rfl
    | cons x xs =>
      simp only [radicalPhaseEval]
      simp only [Bool.false_xor]
      rw [ih xs (Bool.xor c (b && x)), ih xs (b && x)]
      cases c <;> cases (b && x) <;> cases radicalPhaseEval bs xs false <;> rfl

theorem pairPhaseEval_offset (ps xs : List (Bool × Bool)) (c : Bool) :
    pairPhaseEval ps xs c = Bool.xor c (pairPhaseEval ps xs false) := by
  induction ps generalizing xs c with
  | nil => cases c <;> rfl
  | cons p ps ih =>
    cases xs with
    | nil => cases c <;> rfl
    | cons x xs =>
      rcases p with ⟨a,b⟩
      rcases x with ⟨u,v⟩
      simp only [pairPhaseEval]
      simp only [Bool.false_xor]
      rw [ih xs (Bool.xor c (hyperbolicPhase a b u v)), ih xs (hyperbolicPhase a b u v)]
      cases c <;> cases hyperbolicPhase a b u v <;> cases pairPhaseEval ps xs false <;> rfl

theorem radicalPhaseEval_shift (bs ds xs : List Bool) (c : Bool)
    (h : bs.length = ds.length) :
    Bool.xor (radicalPhaseEval bs xs c) (radicalLinearEval ds xs) =
      radicalPhaseEval (radicalCoefficientsXor bs ds) xs c := by
  induction bs generalizing ds xs c with
  | nil => cases ds <;> simp_all [radicalPhaseEval, radicalLinearEval, radicalCoefficientsXor]
  | cons b bs ih =>
    cases ds with
    | nil => simp at h
    | cons d ds =>
      cases xs with
      | nil => simp [radicalPhaseEval, radicalLinearEval, radicalCoefficientsXor]
      | cons x xs =>
        have ht : bs.length = ds.length := by simpa using h
        simp only [radicalPhaseEval, radicalLinearEval, radicalCoefficientsXor]
        have hx := ih ds xs false ht
        have hp := ih ds xs true ht
        have ho := radicalPhaseEval_offset (radicalCoefficientsXor bs ds) xs true
        simp only [Bool.true_xor] at ho
        cases c <;> cases b <;> cases d <;> cases x <;>
          simp_all [Bool.xor_assoc]

theorem pairPhaseEval_shift (ps qs xs : List (Bool × Bool)) (c : Bool)
    (h : ps.length = qs.length) :
    Bool.xor (pairPhaseEval ps xs c) (pairLinearEval qs xs) =
      pairPhaseEval (pairCoefficientsXor ps qs) xs c := by
  induction ps generalizing qs xs c with
  | nil => cases qs <;> simp_all [pairPhaseEval, pairLinearEval, pairCoefficientsXor]
  | cons p ps ih =>
    cases qs with
    | nil => simp at h
    | cons q qs =>
      cases xs with
      | nil => simp [pairPhaseEval, pairLinearEval, pairCoefficientsXor]
      | cons x xs =>
        rcases p with ⟨a,b⟩
        rcases q with ⟨d,e⟩
        rcases x with ⟨u,v⟩
        have ht : ps.length = qs.length := by simpa using h
        simp only [pairPhaseEval, pairLinearEval, pairCoefficientsXor]
        have hx := ih qs xs false ht
        have hp := ih qs xs true ht
        have ho := pairPhaseEval_offset (pairCoefficientsXor ps qs) xs true
        simp only [Bool.true_xor] at ho
        cases c <;> cases a <;> cases b <;> cases d <;> cases e <;> cases u <;> cases v <;>
          simp_all [hyperbolicPhase, Bool.xor_assoc]


end SectorSimulation
