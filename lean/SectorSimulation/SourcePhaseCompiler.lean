import SectorSimulation.ZeroWirePhaseBoundary
import SectorSimulation.PhaseCompilerSize
namespace SectorSimulation

theorem circuitDescriptor_has_wire {n : Nat} (d : CircuitDescriptor n) : 0 < n := by
  have h := d.output.isLt
  omega

theorem noZeroWireCircuitDescriptor : ¬ Nonempty (CircuitDescriptor 0) := by
  intro h
  obtain ⟨d⟩ := h
  exact Fin.elim0 d.output

theorem phaseWithinDegree_sound {n bound : Nat} (phase : PhaseANF n)
    (h : phaseWithinDegree bound phase = true) :
    ∀ m ∈ phase, monomialDegree m ≤ bound := by
  intro m hm
  have hv := List.all_eq_true.mp h m hm
  exact of_decide_eq_true hv

theorem circuitDescriptor_phase_compilation {n : Nat} (d : CircuitDescriptor n)
    (cubic : phasesAreCubic d = true) (state : SharedDyadicState n) :
    ∃ firstRecords firstResult secondRecords secondResult,
      compilePhaseRecords d.output d.firstPhase = some firstRecords ∧
      replayExactNative n firstRecords state = some firstResult ∧
      (∀ x, sharedAmplitude firstResult x = exactOfDyadic
        ⟨if evalPhase d.firstPhase x then cycloNeg (state.numerator x) else state.numerator x, state.exponent⟩) ∧
      compilePhaseRecords d.output d.secondPhase = some secondRecords ∧
      replayExactNative n secondRecords state = some secondResult ∧
      (∀ x, sharedAmplitude secondResult x = exactOfDyadic
        ⟨if evalPhase d.secondPhase x then cycloNeg (state.numerator x) else state.numerator x, state.exponent⟩) ∧
      firstRecords.length ≤ 17 * d.firstPhase.length ∧ secondRecords.length ≤ 17 * d.secondPhase.length := by
  have h1 := (Bool.and_eq_true_iff.mp cubic).1
  have h2 := (Bool.and_eq_true_iff.mp cubic).2
  obtain ⟨r1, s1, hc1, hr1, ha1⟩ := compilePhaseRecords_correct d.output d.firstPhase (phaseWithinDegree_sound d.firstPhase h1) state
  obtain ⟨r2, s2, hc2, hr2, ha2⟩ := compilePhaseRecords_correct d.output d.secondPhase (phaseWithinDegree_sound d.secondPhase h2) state
  exact ⟨r1, s1, r2, s2, hc1, hr1, ha1, hc2, hr2, ha2,
    compilePhaseRecords_length d.output d.firstPhase r1 hc1,
    compilePhaseRecords_length d.output d.secondPhase r2 hc2⟩

end SectorSimulation
