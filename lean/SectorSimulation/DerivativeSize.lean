import SectorSimulation.CubicDerivativeANF
namespace SectorSimulation

theorem cubicMaskDerivativeTerms_length {n : Nat} (m : Monomial n) (j : BinaryVector n)
    (terms : List (QuadraticTerm n)) (h : cubicMaskDerivativeTerms m j = some terms) :
    terms.length ≤ 7 := by
  unfold cubicMaskDerivativeTerms at h
  split at h
  · simp_all
  · rename_i i hi
    simp only [Option.some.injEq] at h
    subst terms
    cases hj : j i <;> simp [linearDerivativeTerms, conditionalQuadraticTerm, hj]
  · rename_i i k hi
    simp only [Option.some.injEq] at h
    subst terms
    cases hj : j i <;> cases hk : j k <;> simp [quadraticDerivativeTerms, conditionalQuadraticTerm, hj, hk]
  · rename_i i k l hi
    simp only [Option.some.injEq] at h
    subst terms
    cases hj : j i <;> cases hk : j k <;> cases hl : j l <;> simp [cubicDerivativeTerms, conditionalQuadraticTerm, hj, hk, hl]
  · contradiction

theorem cubicPhaseDerivativeTerms_length {n : Nat} (p : PhaseANF n) (j : BinaryVector n)
    (terms : List (QuadraticTerm n)) (h : cubicPhaseDerivativeTerms p j = some terms) :
    terms.length ≤ 7 * p.length := by
  induction p generalizing terms with
  | nil => simp [cubicPhaseDerivativeTerms] at h; subst terms; simp
  | cons m rest ih =>
    simp only [cubicPhaseDerivativeTerms] at h
    cases hm : cubicMaskDerivativeTerms m j with
    | none => simp [hm] at h
    | some a =>
      cases hr : cubicPhaseDerivativeTerms rest j with
      | none => simp [hm, hr] at h
      | some b =>
        simp [hm, hr] at h
        subst terms
        have ha := cubicMaskDerivativeTerms_length m j a hm
        have hb := ih b hr
        simp only [List.length_append, List.length_cons, Nat.mul_succ]
        omega

theorem cubicPhaseDerivativeANF_length {n : Nat} (p : PhaseANF n) (j : BinaryVector n)
    (q : PhaseANF n) (h : cubicPhaseDerivativeANF p j = some q) :
    q.length ≤ 7 * p.length := by
  unfold cubicPhaseDerivativeANF at h
  cases ht : cubicPhaseDerivativeTerms p j with
  | none => simp [ht] at h
  | some terms =>
    simp [ht] at h
    subst q
    simpa [quadraticTermsToANF] using cubicPhaseDerivativeTerms_length p j terms ht
end SectorSimulation
