import SectorSimulation.QuadraticMasks
namespace SectorSimulation

theorem quadraticTermMask_degree {n : Nat} (term : QuadraticTerm n) :
    monomialDegree (quadraticTermMask term) ≤ 2 := by
  cases term with
  | constant =>
    have h : (List.finRange n).filter (fun _ => false) = [] := by
      apply List.filter_eq_nil_iff.mpr
      simp
    simp [quadraticTermMask, monomialDegree, h]
  | linear i =>
    have h : singletonMask i = pairMask i i := by
      funext t
      simp [singletonMask, pairMask]
    simpa [quadraticTermMask, h] using pairMask_degree i i
  | product i k => exact pairMask_degree i k

theorem quadraticTermsToANF_degree {n : Nat} (terms : List (QuadraticTerm n)) :
    phaseWithinDegree 2 (quadraticTermsToANF terms) = true := by
  simp [phaseWithinDegree, quadraticTermsToANF, quadraticTermMask_degree]

def cubicPhaseDerivativeANF {n : Nat} (p : PhaseANF n) (j : BinaryVector n) : Option (PhaseANF n) :=
  (cubicPhaseDerivativeTerms p j).map quadraticTermsToANF

theorem cubicPhaseDerivativeANF_correct {n : Nat} (p : PhaseANF n)
    (j : BinaryVector n) (hdegree : phaseWithinDegree 3 p = true) :
    ∃ q, cubicPhaseDerivativeANF p j = some q ∧ phaseWithinDegree 2 q = true ∧
      ∀ x, evalPhase q x = booleanDerivative (evalPhase p) (binaryShift j) x := by
  obtain ⟨terms, hterms, heval⟩ := cubicPhaseDerivativeTerms_correct p j hdegree
  refine ⟨quadraticTermsToANF terms, ?_, quadraticTermsToANF_degree terms, ?_⟩
  · simp [cubicPhaseDerivativeANF, hterms]
  · intro x
    rw [evalQuadraticTerms_bitMasks, heval x]

end SectorSimulation
