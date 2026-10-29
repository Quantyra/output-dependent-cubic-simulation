import SectorSimulation.PhaseBlockCompiler
namespace SectorSimulation

theorem phaseBlock_records_length {n : Nat} (block : PhaseBlock n) : block.records.length ≤ 17 := by
  cases block with
  | lower term => cases term <;> simp [PhaseBlock.records, lowerPhaseRecords]
  | cubic a b c => simp [PhaseBlock.records, threeWireCubicProgram, threeWireToffoli]

theorem phaseBlockRecords_length {n : Nat} (blocks : List (PhaseBlock n)) :
    (phaseBlockRecords blocks).length ≤ 17 * blocks.length := by
  induction blocks with
  | nil => simp [phaseBlockRecords]
  | cons block rest ih =>
    have hb := phaseBlock_records_length block
    simp only [phaseBlockRecords, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

theorem compilePhaseBlocks_length {n : Nat} (anchor : Fin n) (phase : PhaseANF n) (blocks : List (PhaseBlock n))
    (h : compilePhaseBlocks anchor phase = some blocks) : blocks.length = phase.length := by
  induction phase generalizing blocks with
  | nil => simp [compilePhaseBlocks] at h; subst blocks; rfl
  | cons m rest ih =>
    cases hm : compilePhaseMask anchor m with
    | none => simp [compilePhaseBlocks, hm] at h
    | some block =>
      cases hr : compilePhaseBlocks anchor rest with
      | none => simp [compilePhaseBlocks, hm, hr] at h
      | some tail =>
        simp [compilePhaseBlocks, hm, hr] at h
        subst blocks
        simp only [List.length_cons]
        rw [ih tail hr]

theorem compilePhaseRecords_length {n : Nat} (anchor : Fin n) (phase : PhaseANF n) (records : List NativeGate)
    (h : compilePhaseRecords anchor phase = some records) : records.length ≤ 17 * phase.length := by
  cases hb : compilePhaseBlocks anchor phase with
  | none => simp [compilePhaseRecords, hb] at h
  | some blocks =>
    simp [compilePhaseRecords, hb] at h
    subst records
    rw [← compilePhaseBlocks_length anchor phase blocks hb]
    exact phaseBlockRecords_length blocks

end SectorSimulation
