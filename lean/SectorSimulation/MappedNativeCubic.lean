import SectorSimulation.HadamardAmplitudeCongruence
namespace SectorSimulation

theorem runThreeWireProgram_append {n : Nat} (w : Fin 3 → Fin n)
    (a b : List ThreeWireGate) (state : SharedDyadicState n) :
    runThreeWireProgram w (a ++ b) state = runThreeWireProgram w b (runThreeWireProgram w a state) := by
  induction a generalizing state with
  | nil => rfl
  | cons gate rest ih => simpa [runThreeWireProgram] using ih (runThreeWireGate w gate state)

def threeWireCubicProgram : List ThreeWireGate :=
  .hadamard 2 :: (threeWireToffoli ++ [.hadamard 2])

theorem threeWireCubicProgram_valid : ∀ gate ∈ threeWireCubicProgram, gate.valid := by
  intro gate h
  simp only [threeWireCubicProgram, List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with h | h | h
  · subst gate; trivial
  · exact threeWireToffoli_valid gate h
  · subst gate; trivial

theorem threeWireCubicProgram_action {n : Nat} (w : Fin 3 → Fin n) (state : SharedDyadicState n) :
    runThreeWireProgram w threeWireCubicProgram state = sharedHadamard (w 2)
      (runThreeWireProgram w threeWireToffoli (sharedHadamard (w 2) state)) := by
  simp [threeWireCubicProgram, runThreeWireProgram, runThreeWireGate, runThreeWireProgram_append]

theorem mappedNativeCubic_correct {n : Nat} (w : Fin 3 → Fin n) (hw : Function.Injective w)
    (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (threeWireCubicProgram.map (mappedNativeGate w)) state = some result ∧
      ∀ x, sharedAmplitude result x = sharedAmplitude (sharedCubicSign (w 0) (w 1) (w 2) state) x := by
  refine ⟨runThreeWireProgram w threeWireCubicProgram state,
    mappedNativeProgram_correct w hw threeWireCubicProgram threeWireCubicProgram_valid state, ?_⟩
  intro x
  rw [threeWireCubicProgram_action]
  exact mappedToffoli_cubic_sign w hw state x

end SectorSimulation
