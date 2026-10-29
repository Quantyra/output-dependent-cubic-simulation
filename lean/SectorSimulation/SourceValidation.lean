import SectorSimulation.SourceOutputPivot
namespace SectorSimulation

def matrixSymmetric {n : Nat} (J : BinaryMatrix n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun k => J i k == J k i

theorem matrixSymmetric_correct {n : Nat} (J : BinaryMatrix n) :
    matrixSymmetric J = true ↔ ∀ i k, J i k = J k i := by
  simp only [matrixSymmetric, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h i k; exact h i (List.mem_finRange i) k (List.mem_finRange k)
  · intro h i _ k _; exact h i k

def sourceDescriptorValid {n : Nat} (d : CircuitDescriptor n) : Bool :=
  phasesAreCubic d && matrixSymmetric d.pairing && (gaussianRowProgram d.pairing).isSome

theorem sourceDescriptorValid_correct {n : Nat} (d : CircuitDescriptor n) :
    sourceDescriptorValid d = true ↔
      phasesAreCubic d = true ∧ (∀ i k, d.pairing i k = d.pairing k i) ∧
        (∀ x z, matrixApply d.pairing x = matrixApply d.pairing z → x = z) := by
  simp only [sourceDescriptorValid, Bool.and_eq_true, matrixSymmetric_correct, Option.isSome_iff_exists]
  constructor
  · rintro ⟨⟨hc, hs⟩, hp⟩
    exact ⟨hc, hs, (gaussianRowProgram_success_iff_injective d.pairing).mp hp⟩
  · rintro ⟨hc, hs, hi⟩
    exact ⟨⟨hc, hs⟩, (gaussianRowProgram_success_iff_injective d.pairing).mpr hi⟩

theorem validatedSourceOutputDerivative {n : Nat} (d : CircuitDescriptor n)
    (hvalid : sourceDescriptorValid d = true) :
    ∃ j q, sourceOutputDerivativePivot d = some (j, q) ∧
      matrixApply d.pairing j = outputUnit d ∧ j ≠ zeroVector ∧
      (∀ z, matrixApply d.pairing z = outputUnit d → z = j) ∧
      phaseWithinDegree 2 q = true ∧ q.length ≤ 7 * d.secondPhase.length ∧
      ∀ x, evalPhase q x = secondPhaseDerivative d j x := by
  have hv := (sourceDescriptorValid_correct d).mp hvalid
  exact sourceOutputDerivativePivot_correct d hv.1 hv.2.2

end SectorSimulation
