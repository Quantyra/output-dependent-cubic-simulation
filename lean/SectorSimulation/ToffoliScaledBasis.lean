import SectorSimulation.ExactReplayShift
namespace SectorSimulation

theorem sharedShiftScale_amplitude {n : Nat} (k : Cyclo8) (d : Nat)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    sharedAmplitude (sharedShift d (sharedScale k state)) x =
      exactMul (exactOfDyadic ⟨k, d⟩) (sharedAmplitude state x) := by
  change exactOfDyadic _ = exactMul (exactOfDyadic _) (exactOfDyadic _)
  rw [exact_mul_representatives]
  simp [sharedShift, sharedScale, dyadicMultiply, Nat.add_comm, cycloMul]
  rfl

theorem toffoliScaledShiftedBasis_correct (input output : Fin 8) (k : Cyclo8) (d : Nat) :
    ∃ result, replayExactNative 3 nativeToffoli012 (sharedShift d (sharedScale k (threeBitBasis input))) = some result ∧
      sharedAmplitude result (threeBitVector output) =
        sharedAmplitude (sharedShift d (sharedScale k (threeBitBasis (threeBitToffoliOutput input)))) (threeBitVector output) := by
  obtain ⟨result, hr, he⟩ := toffoliScaledShiftedBasis_replay input output k d
  refine ⟨sharedShift d (sharedScale k result), hr, ?_⟩
  rw [sharedShiftScale_amplitude, sharedShiftScale_amplitude, he]

end SectorSimulation
