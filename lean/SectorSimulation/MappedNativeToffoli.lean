import SectorSimulation.ThreeWireProgram
namespace SectorSimulation

def mappedNativeGate {n : Nat} (w : Fin 3 → Fin n) : ThreeWireGate → NativeGate
  | .hadamard i => ⟨"H", [(w i).val]⟩
  | .x i => ⟨"X", [(w i).val]⟩
  | .z i => ⟨"Z", [(w i).val]⟩
  | .t i false => ⟨"T", [(w i).val]⟩
  | .t i true => ⟨"TDG", [(w i).val]⟩
  | .cnot c t => ⟨"CX", [(w c).val, (w t).val]⟩

def ThreeWireGate.valid : ThreeWireGate → Prop
  | .cnot c dst => c ≠ dst
  | _ => True

theorem mappedNativeGate_correct {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (gate : ThreeWireGate) (valid : gate.valid) (state : SharedDyadicState n) :
    applyExactNative n (mappedNativeGate w gate) state = some (runThreeWireGate w gate state) := by
  cases gate with
  | hadamard i => simp [mappedNativeGate, applyExactNative, runThreeWireGate, (w i).isLt]
  | x i => simp [mappedNativeGate, applyExactNative, runThreeWireGate, (w i).isLt]
  | z i => simp [mappedNativeGate, applyExactNative, runThreeWireGate, (w i).isLt]
  | t i inverse => cases inverse <;> simp [mappedNativeGate, applyExactNative, runThreeWireGate, (w i).isLt]
  | cnot c t =>
    have hct : c ≠ t := valid
    have hval : (w c).val ≠ (w t).val := by
      intro h
      exact hct (hw (Fin.ext h))
    simp [mappedNativeGate, applyExactNative, runThreeWireGate, (w c).isLt, (w t).isLt, hval]

theorem mappedNativeProgram_correct {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (gates : List ThreeWireGate) (valid : ∀ gate ∈ gates, gate.valid) (state : SharedDyadicState n) :
    replayExactNative n (gates.map (mappedNativeGate w)) state = some (runThreeWireProgram w gates state) := by
  induction gates generalizing state with
  | nil => rfl
  | cons gate rest ih =>
    have hg : gate.valid := valid gate (by simp)
    have hr : ∀ g ∈ rest, g.valid := by intro g h; exact valid g (by simp [h])
    simp only [List.map_cons, replayExactNative, runThreeWireProgram]
    rw [mappedNativeGate_correct w hw gate hg]
    exact ih hr _

theorem threeWireToffoli_valid : ∀ gate ∈ threeWireToffoli, gate.valid := by
  simp [threeWireToffoli, ThreeWireGate.valid]

theorem mappedNativeToffoli_correct {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    ∃ result, replayExactNative n (threeWireToffoli.map (mappedNativeGate w)) state = some result ∧
      sharedAmplitude result x = sharedAmplitude (sharedToffoli (w 0) (w 1) (w 2) state) x := by
  exact ⟨runThreeWireProgram w threeWireToffoli state,
    mappedNativeProgram_correct w hw threeWireToffoli threeWireToffoli_valid state,
    threeWireToffoli_global_correct w hw state x⟩

end SectorSimulation
