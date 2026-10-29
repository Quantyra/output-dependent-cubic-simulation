import SectorSimulation.ToffoliIdealSum
namespace SectorSimulation

theorem threeBitVector_surjective (x : BinaryVector 3) :
    ∃ k : Fin 8, threeBitVector k = x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2
  · refine ⟨0, ?_⟩
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> first | exact h0.symm | exact h1.symm | exact h2.symm
  · refine ⟨4, ?_⟩
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> first | exact h0.symm | exact h1.symm | exact h2.symm
  · refine ⟨2, ?_⟩
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> first | exact h0.symm | exact h1.symm | exact h2.symm
  · refine ⟨6, ?_⟩
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> first | exact h0.symm | exact h1.symm | exact h2.symm
  · refine ⟨1, ?_⟩
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> first | exact h0.symm | exact h1.symm | exact h2.symm
  · refine ⟨5, ?_⟩
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> first | exact h0.symm | exact h1.symm | exact h2.symm
  · refine ⟨3, ?_⟩
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> first | exact h0.symm | exact h1.symm | exact h2.symm
  · refine ⟨7, ?_⟩
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> first | exact h0.symm | exact h1.symm | exact h2.symm

theorem toffoli_threeBit_all_amplitudes (state : SharedDyadicState 3) :
    ∃ result, replayExactNative 3 nativeToffoli012 state = some result ∧
      ∀ x : BinaryVector 3, sharedAmplitude result x = sharedAmplitude (sharedToffoli 0 1 2 state) x := by
  refine ⟨threeBitReplaySum state, toffoli_threeBit_replay_sum state, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := threeBitVector_surjective x
  rw [← hk]
  exact (toffoliReplaySum_amplitude state k).trans (idealThreeBitSum_correct state k)

end SectorSimulation
