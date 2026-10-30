import SectorSimulation.QuadraticMasks
namespace SectorSimulation

def termPolar {n : Nat} (t : QuadraticTerm n) (u v : BinaryVector n) : Bool :=
  match t with
  | .product i j => Bool.xor (u i && v j) (u j && v i)
  | _ => false

def termsPolar {n : Nat} : List (QuadraticTerm n) → BinaryVector n → BinaryVector n → Bool
  | [], _, _ => false
  | t::ts, u, v => Bool.xor (termPolar t u v) (termsPolar ts u v)

def phasePolar {n : Nat} (p : PhaseANF n) (u v : BinaryVector n) : Bool :=
  Bool.xor (evalPhase p (binaryShift u v))
    (Bool.xor (evalPhase p u) (Bool.xor (evalPhase p v) (evalPhase p (fun _ => false))))

theorem termPolar_correct {n : Nat} (t : QuadraticTerm n) (u v : BinaryVector n) :
    termPolar t u v = Bool.xor (evalQuadraticTerm t (binaryShift u v))
      (Bool.xor (evalQuadraticTerm t u) (Bool.xor (evalQuadraticTerm t v)
        (evalQuadraticTerm t (fun _ => false)))) := by
  cases t with
  | constant => rfl
  | linear i => simp only [termPolar, evalQuadraticTerm, binaryShift]; cases u i <;> cases v i <;> rfl
  | product i j => simp only [termPolar, evalQuadraticTerm, binaryShift]; cases u i <;> cases u j <;> cases v i <;> cases v j <;> rfl

theorem termsPolar_correct {n : Nat} (ts : List (QuadraticTerm n)) (u v : BinaryVector n) :
    termsPolar ts u v = phasePolar (quadraticTermsToANF ts) u v := by
  unfold phasePolar
  simp only [evalQuadraticTerms_bitMasks]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [termsPolar, evalQuadraticTerms]
    rw [termPolar_correct, ih]
    cases evalQuadraticTerm t (binaryShift u v) <;> cases evalQuadraticTerm t u <;>
      cases evalQuadraticTerm t v <;> cases evalQuadraticTerm t (fun _ => false) <;>
      cases evalQuadraticTerms ts (binaryShift u v) <;> cases evalQuadraticTerms ts u <;>
      cases evalQuadraticTerms ts v <;> cases evalQuadraticTerms ts (fun _ => false) <;> rfl

theorem termsPolar_alternating {n : Nat} (ts : List (QuadraticTerm n)) (u : BinaryVector n) :
    termsPolar ts u u = false := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [termsPolar, termPolar, ih, Bool.and_comm]

theorem termsPolar_symmetric {n : Nat} (ts : List (QuadraticTerm n)) (u v : BinaryVector n) :
    termsPolar ts u v = termsPolar ts v u := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [termsPolar, termPolar, ih, Bool.and_comm, Bool.xor_comm]


theorem termPolar_add_left {n : Nat} (t : QuadraticTerm n) (u v w : BinaryVector n) :
    termPolar t (binaryShift u v) w = Bool.xor (termPolar t u w) (termPolar t v w) := by
  cases t with
  | constant => rfl
  | linear i => rfl
  | product i j =>
    simp only [termPolar, binaryShift]
    cases u i <;> cases u j <;> cases v i <;> cases v j <;> cases w i <;> cases w j <;> rfl

theorem termsPolar_add_left {n : Nat} (ts : List (QuadraticTerm n)) (u v w : BinaryVector n) :
    termsPolar ts (binaryShift u v) w = Bool.xor (termsPolar ts u w) (termsPolar ts v w) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [termsPolar, termPolar_add_left, ih]
    cases termPolar t u w <;> cases termPolar t v w <;>
      cases termsPolar ts u w <;> cases termsPolar ts v w <;> rfl

theorem termsPolar_add_right {n : Nat} (ts : List (QuadraticTerm n)) (u v w : BinaryVector n) :
    termsPolar ts u (binaryShift v w) = Bool.xor (termsPolar ts u v) (termsPolar ts u w) := by
  rw [termsPolar_symmetric ts u (binaryShift v w), termsPolar_add_left,
    termsPolar_symmetric ts v u, termsPolar_symmetric ts w u]

def quadraticMaskToTerm {n : Nat} (m : Monomial n) : Option (QuadraticTerm n) :=
  match selectedVariables m with
  | [] => some .constant
  | [i] => some (.linear i)
  | [i,j] => some (.product i j)
  | _ => none

theorem quadraticMaskToTerm_complete {n : Nat} (m : Monomial n) (h : monomialDegree m ≤ 2) :
    ∃ t, quadraticMaskToTerm m = some t := by
  rw [monomialDegree_eq_selectedLength] at h
  unfold quadraticMaskToTerm
  cases hs : selectedVariables m with
  | nil => exact ⟨.«constant», rfl⟩
  | cons i rest =>
    cases rest with
    | nil => exact ⟨.linear i, rfl⟩
    | cons j rest =>
      cases rest with
      | nil => exact ⟨.product i j, rfl⟩
      | cons k rest => simp [hs] at h

theorem quadraticMaskToTerm_correct {n : Nat} (m : Monomial n) (t : QuadraticTerm n)
    (h : quadraticMaskToTerm m = some t) (x : BinaryVector n) :
    evalMonomial m x = evalQuadraticTerm t x := by
  unfold quadraticMaskToTerm at h
  cases hs : selectedVariables m with
  | nil =>
    simp [hs] at h
    subst t
    exact evalMonomial_selected_nil m x hs
  | cons i rest =>
    cases rest with
    | nil =>
      simp [hs] at h
      subst t
      exact evalMonomial_selected_one m x i hs
    | cons j rest =>
      cases rest with
      | nil =>
        simp [hs] at h
        subst t
        exact evalMonomial_selected_two m x i j hs
      | cons k rest => simp [hs] at h


def quadraticSourceTerms {n : Nat} : PhaseANF n → Option (List (QuadraticTerm n))
  | [] => some []
  | m::rest =>
    match quadraticMaskToTerm m, quadraticSourceTerms rest with
    | some t, some ts => some (t::ts)
    | _, _ => none

theorem quadraticSourceTerms_complete {n : Nat} (p : PhaseANF n)
    (hdegree : phaseWithinDegree 2 p = true) :
    ∃ ts, quadraticSourceTerms p = some ts ∧
      ∀ x, evalPhase p x = evalQuadraticTerms ts x := by
  induction p with
  | nil => exact ⟨[], rfl, fun _ => rfl⟩
  | cons m rest ih =>
    have bounds : monomialDegree m ≤ 2 ∧ phaseWithinDegree 2 rest = true := by
      simpa [phaseWithinDegree] using hdegree
    obtain ⟨t, ht⟩ := quadraticMaskToTerm_complete m bounds.1
    obtain ⟨ts, hts, hcorrect⟩ := ih bounds.2
    refine ⟨t::ts, ?_, ?_⟩
    · simp [quadraticSourceTerms, ht, hts]
    · intro x
      rw [evalPhase_cons, evalQuadraticTerms, quadraticMaskToTerm_correct m t ht x, hcorrect x]


theorem sourceQuadratic_hasPolar {n : Nat} (p : PhaseANF n)
    (hdegree : phaseWithinDegree 2 p = true) :
    ∃ ts, quadraticSourceTerms p = some ts ∧
      (∀ x, evalPhase p x = evalQuadraticTerms ts x) ∧
      (∀ u v, phasePolar p u v = termsPolar ts u v) ∧
      (∀ u, termsPolar ts u u = false) ∧
      (∀ u v w, termsPolar ts (binaryShift u v) w = Bool.xor (termsPolar ts u w) (termsPolar ts v w)) ∧
      (∀ u v w, termsPolar ts u (binaryShift v w) = Bool.xor (termsPolar ts u v) (termsPolar ts u w)) := by
  obtain ⟨ts, hts, hcorrect⟩ := quadraticSourceTerms_complete p hdegree
  refine ⟨ts, hts, hcorrect, ?_, termsPolar_alternating ts, termsPolar_add_left ts, termsPolar_add_right ts⟩
  intro u v
  rw [termsPolar_correct]
  unfold phasePolar
  simp only [hcorrect, evalQuadraticTerms_bitMasks]

end SectorSimulation
