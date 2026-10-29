import SectorSimulation.MappedNativeCubic
namespace SectorSimulation

def sharedNeg {n : Nat} (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => cycloNeg (state.numerator x), state.exponent⟩

theorem sharedNeg_amplitude {n : Nat} (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (sharedNeg state) x = exactNeg (sharedAmplitude state x) := by rfl

theorem sharedCubicSign_amplitude_congr {n : Nat} (a b target : Fin n) (u v : SharedDyadicState n)
    (h : ∀ x, sharedAmplitude u x = sharedAmplitude v x) (x : BinaryVector n) :
    sharedAmplitude (sharedCubicSign a b target u) x = sharedAmplitude (sharedCubicSign a b target v) x := by
  cases ha : x a <;> cases hb : x b <;> cases ht : x target <;>
    simp [sharedCubicSign, sharedAmplitude, ha, hb, ht] <;> try exact h x
  change exactNeg (sharedAmplitude u x) = exactNeg (sharedAmplitude v x)
  rw [h x]

theorem replayExactNative_append {n : Nat} (first rest : List NativeGate) (state : SharedDyadicState n) :
    replayExactNative n (first ++ rest) state =
      (replayExactNative n first state).bind (replayExactNative n rest) := by
  induction first generalizing state with
  | nil => rfl
  | cons gate tail ih =>
    simp only [List.cons_append, replayExactNative]
    cases h : applyExactNative n gate state with
    | none => rfl
    | some next => simpa [h] using ih next

def nativeCubicLayer {n : Nat} (wires : List (Fin 3 → Fin n)) : List NativeGate :=
  wires.flatMap (fun w => threeWireCubicProgram.map (mappedNativeGate w))

def idealCubicLayer {n : Nat} : List (Fin 3 → Fin n) → SharedDyadicState n → SharedDyadicState n
  | [], state => state
  | w :: rest, state => idealCubicLayer rest (sharedCubicSign (w 0) (w 1) (w 2) state)

theorem nativeCubicLayer_correct_from_equivalent {n : Nat} (wires : List (Fin 3 → Fin n))
    (valid : ∀ w ∈ wires, Function.Injective w) (u v : SharedDyadicState n)
    (equiv : ∀ x, sharedAmplitude u x = sharedAmplitude v x) :
    ∃ result, replayExactNative n (nativeCubicLayer wires) u = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (idealCubicLayer wires v) x := by
  induction wires generalizing u v with
  | nil => exact ⟨u, rfl, equiv⟩
  | cons w rest ih =>
    have hw : Function.Injective w := valid w (by simp)
    have hr : ∀ z ∈ rest, Function.Injective z := by intro z hz; exact valid z (by simp [hz])
    obtain ⟨mid, hm, ha⟩ := mappedNativeCubic_correct w hw u
    have he : ∀ x, sharedAmplitude mid x = sharedAmplitude (sharedCubicSign (w 0) (w 1) (w 2) v) x := by
      intro x
      exact (ha x).trans (sharedCubicSign_amplitude_congr (w 0) (w 1) (w 2) u v equiv x)
    obtain ⟨result, hresult, heq⟩ := ih hr mid (sharedCubicSign (w 0) (w 1) (w 2) v) he
    refine ⟨result, ?_, heq⟩
    simp only [nativeCubicLayer, List.flatMap_cons, replayExactNative_append, hm]
    exact hresult

theorem nativeCubicLayer_correct {n : Nat} (wires : List (Fin 3 → Fin n))
    (valid : ∀ w ∈ wires, Function.Injective w) (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (nativeCubicLayer wires) state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (idealCubicLayer wires state) x := by
  exact nativeCubicLayer_correct_from_equivalent wires valid state state (fun _ => rfl)

end SectorSimulation
