import SectorSimulation.ExhaustiveMatrixSolve
namespace SectorSimulation

def outputUnit {n : Nat} (d : CircuitDescriptor n) : BinaryVector n := singletonMask d.output

def sourceOutputDerivativeExhaustive {n : Nat} (d : CircuitDescriptor n) : Option (BinaryVector n × PhaseANF n) :=
  match solveMatrixExhaustive d.pairing (outputUnit d) with
  | none => none
  | some j => (cubicPhaseDerivativeANF d.secondPhase j).map fun q => (j, q)

theorem sourceOutputDerivativeExhaustive_correct {n : Nat} (d : CircuitDescriptor n)
    (hcubic : phasesAreCubic d = true)
    (hsurj : ∀ target, ∃ v, matrixApply d.pairing v = target) :
    ∃ j q, sourceOutputDerivativeExhaustive d = some (j, q) ∧
      matrixApply d.pairing j = outputUnit d ∧
      phaseWithinDegree 2 q = true ∧ q.length ≤ 7 * d.secondPhase.length ∧
      ∀ x, evalPhase q x = secondPhaseDerivative d j x := by
  have hdeg : phaseWithinDegree 3 d.secondPhase = true := by
    have h := (Bool.and_eq_true_iff.mp hcubic).2
    exact h
  obtain ⟨w, hw⟩ := hsurj (outputUnit d)
  obtain ⟨j, hj⟩ := solveMatrixExhaustive_complete d.pairing (outputUnit d) w hw
  have hmatrix := solveMatrixExhaustive_sound d.pairing (outputUnit d) j hj
  obtain ⟨q, hq, hqdeg, hqeval⟩ := cubicPhaseDerivativeANF_correct d.secondPhase j hdeg
  have hsize := cubicPhaseDerivativeANF_length d.secondPhase j q hq
  refine ⟨j, q, ?_, hmatrix, hqdeg, hsize, ?_⟩
  · simp [sourceOutputDerivativeExhaustive, hj, hq]
  · intro x
    exact hqeval x

end SectorSimulation
