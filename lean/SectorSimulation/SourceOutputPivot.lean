import SectorSimulation.PivotComplete
namespace SectorSimulation

def sourceOutputDerivativePivot {n : Nat} (d : CircuitDescriptor n) : Option (BinaryVector n × PhaseANF n) :=
  match gaussianSolveChecked d.pairing (outputUnit d) with
  | none => none
  | some j => (cubicPhaseDerivativeANF d.secondPhase j).map fun q => (j, q)

theorem sourceOutputDerivativePivot_correct {n : Nat} (d : CircuitDescriptor n)
    (hcubic : phasesAreCubic d = true)
    (hinj : ∀ x z, matrixApply d.pairing x = matrixApply d.pairing z → x = z) :
    ∃ j q, sourceOutputDerivativePivot d = some (j, q) ∧
      matrixApply d.pairing j = outputUnit d ∧ j ≠ zeroVector ∧
      (∀ z, matrixApply d.pairing z = outputUnit d → z = j) ∧
      phaseWithinDegree 2 q = true ∧ q.length ≤ 7 * d.secondPhase.length ∧
      ∀ x, evalPhase q x = secondPhaseDerivative d j x := by
  have hdeg : phaseWithinDegree 3 d.secondPhase = true := (Bool.and_eq_true_iff.mp hcubic).2
  obtain ⟨j, hj⟩ := gaussianSolveChecked_complete_of_injective d.pairing hinj (outputUnit d)
  have hmatrix := gaussianSolveChecked_sound d.pairing (outputUnit d) j hj
  have hnonzero : j ≠ zeroVector := by
    intro hz
    have he : outputUnit d = zeroVector := by
      rw [hz, matrixApply_zero] at hmatrix
      exact hmatrix.symm
    have hi := congrFun he d.output
    simp [outputUnit, singletonMask, zeroVector] at hi
  have hunique : ∀ z, matrixApply d.pairing z = outputUnit d → z = j := by
    intro z hz; exact hinj z j (hz.trans hmatrix.symm)
  obtain ⟨q, hq, hqdeg, hqeval⟩ := cubicPhaseDerivativeANF_correct d.secondPhase j hdeg
  have hsize := cubicPhaseDerivativeANF_length d.secondPhase j q hq
  refine ⟨j, q, ?_, hmatrix, hnonzero, hunique, hqdeg, hsize, ?_⟩
  · simp [sourceOutputDerivativePivot, hj, hq]
  · intro x; exact hqeval x

end SectorSimulation
