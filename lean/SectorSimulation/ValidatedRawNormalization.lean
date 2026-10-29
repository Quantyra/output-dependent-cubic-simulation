import SectorSimulation.RawDescriptorNormalization
namespace SectorSimulation

def normalizeAfterRawValidation (raw : RawTwoPhaseDescriptor) : Option RawTwoPhaseDescriptor := do
  let _ ← rawDescriptorToValidated raw
  pure (normalizeRawDescriptor raw)

theorem normalizeAfterRawValidation_rejects (raw : RawTwoPhaseDescriptor)
    (h : rawDescriptorToValidated raw = none) : normalizeAfterRawValidation raw = none := by
  simp [normalizeAfterRawValidation, h]

theorem normalizeAfterRawValidation_accepts (raw : RawTwoPhaseDescriptor) (n : Nat)
    (d : CircuitDescriptor n) (h : rawDescriptorToValidated raw = some ⟨n, d⟩) :
    normalizeAfterRawValidation raw = some (normalizeRawDescriptor raw) := by
  simp [normalizeAfterRawValidation, h]

end SectorSimulation
