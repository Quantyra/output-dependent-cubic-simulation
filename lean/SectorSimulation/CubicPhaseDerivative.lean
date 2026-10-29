import SectorSimulation.CubicMaskDerivative

/-!
Lift the computed one-mask derivative terms across a represented cubic phase.
The output remains in the auxiliary quadratic term language; bit-mask ANF
translation, cost accounting and native circuit semantics remain separate.
-/

namespace SectorSimulation

/-- Construct and concatenate the derivative terms for a whole phase. -/
def cubicPhaseDerivativeTerms {n : Nat} :
    PhaseANF n → BinaryVector n → Option (List (QuadraticTerm n))
  | [], _ => some []
  | m :: rest, j =>
    match cubicMaskDerivativeTerms m j, cubicPhaseDerivativeTerms rest j with
    | some first, some tail => some (first ++ tail)
    | _, _ => none

/-- A cubic source phase has a constructed quadratic term list whose value
is its Boolean derivative at every binary input. -/
theorem cubicPhaseDerivativeTerms_correct {n : Nat} (p : PhaseANF n)
    (j : BinaryVector n) (hdegree : phaseWithinDegree 3 p = true) :
    ∃ terms, cubicPhaseDerivativeTerms p j = some terms ∧
      ∀ x, evalQuadraticTerms terms x =
        booleanDerivative (evalPhase p) (binaryShift j) x := by
  induction p with
  | nil =>
    refine ⟨[], rfl, ?_⟩
    intro x
    rfl
  | cons m rest ih =>
    have bounds : monomialDegree m ≤ 3 ∧ phaseWithinDegree 3 rest = true := by
      simpa [phaseWithinDegree] using hdegree
    obtain ⟨first, hfirst, firstCorrect⟩ := cubicMaskDerivativeTerms_correct m j bounds.1
    obtain ⟨tail, htail, tailCorrect⟩ := ih bounds.2
    refine ⟨first ++ tail, ?_, ?_⟩
    · simp [cubicPhaseDerivativeTerms, hfirst, htail]
    · intro x
      rw [evalQuadraticTerms_append, firstCorrect x, tailCorrect x]
      have heval : evalPhase (m :: rest) =
          fun v => Bool.xor (evalMonomial m v) (evalPhase rest v) := by
        funext v
        simpa [evalPhase] using evalPhase_append [m] rest v
      rw [heval]
      exact (booleanDerivative_xor (evalMonomial m) (evalPhase rest) (binaryShift j) x).symm

end SectorSimulation
