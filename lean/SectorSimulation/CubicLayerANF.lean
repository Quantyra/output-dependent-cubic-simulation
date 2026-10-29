import SectorSimulation.CubicLayerReplay
import SectorSimulation.CubicPhaseDerivative
namespace SectorSimulation

def tripleMask {n : Nat} (w : Fin 3 → Fin n) : Monomial n :=
  fun i => decide (i = w 0 ∨ i = w 1 ∨ i = w 2)

def cubicLayerANF {n : Nat} (wires : List (Fin 3 → Fin n)) : PhaseANF n :=
  wires.map tripleMask

theorem tripleMask_eval {n : Nat} (w : Fin 3 → Fin n) (x : BinaryVector n) :
    evalMonomial (tripleMask w) x = (x (w 0) && x (w 1) && x (w 2)) := by
  apply Bool.eq_iff_iff.mpr
  rw [evalMonomial_eq_true_iff]
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨⟨h (w 0) (by simp [tripleMask]), h (w 1) (by simp [tripleMask])⟩,
      h (w 2) (by simp [tripleMask])⟩
  · intro h i hi
    simp only [tripleMask, decide_eq_true_eq] at hi
    rcases hi with hi | hi | hi <;> subst i
    exact h.1.1
    exact h.1.2
    exact h.2

theorem idealCubicLayer_phase {n : Nat} (wires : List (Fin 3 → Fin n))
    (state : SharedDyadicState n) (x : BinaryVector n) :
    (idealCubicLayer wires state).numerator x =
      if evalPhase (cubicLayerANF wires) x then cycloNeg (state.numerator x) else state.numerator x := by
  induction wires generalizing state with
  | nil => simp [idealCubicLayer, cubicLayerANF, evalPhase]
  | cons w rest ih =>
    simp only [idealCubicLayer, ih, cubicLayerANF, List.map_cons, evalPhase_cons, tripleMask_eval, sharedCubicSign]
    cases h : (x (w 0) && x (w 1) && x (w 2)) <;>
      cases ht : evalPhase (List.map tripleMask rest) x <;>
      simp [h, ht, cycloNeg]
    all_goals cases state.numerator x <;> simp [cycloNeg]

theorem idealCubicLayer_exponent {n : Nat} (wires : List (Fin 3 → Fin n))
    (state : SharedDyadicState n) : (idealCubicLayer wires state).exponent = state.exponent := by
  induction wires generalizing state with
  | nil => rfl
  | cons w rest ih => simpa [idealCubicLayer, sharedCubicSign] using ih (sharedCubicSign (w 0) (w 1) (w 2) state)

theorem nativeCubicLayer_anf {n : Nat} (wires : List (Fin 3 → Fin n))
    (valid : ∀ w ∈ wires, Function.Injective w) (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (nativeCubicLayer wires) state = some result ∧
      ∀ x, sharedAmplitude result x = exactOfDyadic
        ⟨if evalPhase (cubicLayerANF wires) x then cycloNeg (state.numerator x) else state.numerator x,
          state.exponent⟩ := by
  obtain ⟨result, hr, ha⟩ := nativeCubicLayer_correct wires valid state
  refine ⟨result, hr, ?_⟩
  intro x
  rw [ha x]
  simp [sharedAmplitude, idealCubicLayer_phase, idealCubicLayer_exponent]

end SectorSimulation
