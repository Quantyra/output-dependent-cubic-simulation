import SectorSimulation.LowerPhaseNative
namespace SectorSimulation

def lowerPhaseANF {n : Nat} (terms : List (LowerPhaseTerm n)) : PhaseANF n := terms.map lowerPhaseMask

theorem idealLowerPhaseLayer_phase {n : Nat} (terms : List (LowerPhaseTerm n))
    (state : SharedDyadicState n) (x : BinaryVector n) :
    (idealLowerPhaseLayer terms state).numerator x =
      if evalPhase (lowerPhaseANF terms) x then cycloNeg (state.numerator x) else state.numerator x := by
  induction terms generalizing state with
  | nil => simp [idealLowerPhaseLayer, lowerPhaseANF, evalPhase]
  | cons term rest ih =>
    simp only [idealLowerPhaseLayer, ih, lowerPhaseANF, List.map_cons, evalPhase_cons, sharedMonomialSign]
    cases h : evalMonomial (lowerPhaseMask term) x <;>
      cases ht : evalPhase (List.map lowerPhaseMask rest) x <;> simp [h, ht, cycloNeg]
    all_goals cases state.numerator x <;> simp [cycloNeg]

theorem idealLowerPhaseLayer_exponent {n : Nat} (terms : List (LowerPhaseTerm n))
    (state : SharedDyadicState n) : (idealLowerPhaseLayer terms state).exponent = state.exponent := by
  induction terms generalizing state with
  | nil => rfl
  | cons term rest ih => simpa [idealLowerPhaseLayer, sharedMonomialSign] using ih (sharedMonomialSign (lowerPhaseMask term) state)

def combinedPhaseANF {n : Nat} (terms : List (LowerPhaseTerm n)) (wires : List (Fin 3 → Fin n)) : PhaseANF n :=
  lowerPhaseANF terms ++ cubicLayerANF wires

def combinedPhaseRecords {n : Nat} (terms : List (LowerPhaseTerm n)) (wires : List (Fin 3 → Fin n)) : List NativeGate :=
  nativeLowerPhaseLayer terms ++ nativeCubicLayer wires

theorem combinedPhaseNative_correct {n : Nat} (terms : List (LowerPhaseTerm n)) (wires : List (Fin 3 → Fin n))
    (validLower : ∀ term ∈ terms, term.valid) (validCubic : ∀ w ∈ wires, Function.Injective w)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (combinedPhaseRecords terms wires) state = some result ∧
      ∀ x, sharedAmplitude result x = exactOfDyadic
        ⟨if evalPhase (combinedPhaseANF terms wires) x then cycloNeg (state.numerator x) else state.numerator x,
          state.exponent⟩ := by
  obtain ⟨mid, hm, he⟩ := nativeLowerPhaseLayer_correct terms validLower state
  obtain ⟨result, hr, ha⟩ := nativeCubicLayer_correct_from_equivalent wires validCubic mid
    (idealLowerPhaseLayer terms state) he
  refine ⟨result, ?_, ?_⟩
  · simp only [combinedPhaseRecords, replayExactNative_append, hm]
    exact hr
  · intro x
    rw [ha x]
    simp only [sharedAmplitude, idealCubicLayer_phase, idealCubicLayer_exponent,
      idealLowerPhaseLayer_phase, idealLowerPhaseLayer_exponent, combinedPhaseANF, evalPhase_append]
    cases hl : evalPhase (lowerPhaseANF terms) x <;>
      cases hc : evalPhase (cubicLayerANF wires) x <;> simp [hl, hc, cycloNeg]
    all_goals cases state.numerator x <;> simp [cycloNeg]

end SectorSimulation
