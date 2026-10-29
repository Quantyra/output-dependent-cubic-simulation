import SectorSimulation.ThreeBitDecomposition
namespace SectorSimulation

noncomputable def toffoliBasisResult (k : Fin 8) : SharedDyadicState 3 :=
  Classical.choose (toffoliBasisReplay_correct k 0)

theorem toffoliBasisResult_replay (k : Fin 8) :
    replayExactNative 3 nativeToffoli012 (threeBitBasis k) = some (toffoliBasisResult k) :=
  (Classical.choose_spec (toffoliBasisReplay_correct k 0)).1

noncomputable def weightedBasisResult (state : SharedDyadicState 3) (k : Fin 8) : SharedDyadicState 3 :=
  sharedShift state.exponent (sharedScale (state.numerator (threeBitVector k)) (toffoliBasisResult k))

theorem weightedBasis_replay (state : SharedDyadicState 3) (k : Fin 8) :
    replayExactNative 3 nativeToffoli012 (weightedBasis state k) = some (weightedBasisResult state k) := by
  simp [weightedBasis, weightedBasisResult, replayExactNative_shift, replayExactNative_scale, toffoliBasisResult_replay]

theorem weightedBasis_exponent (state : SharedDyadicState 3) (k : Fin 8) :
    (weightedBasis state k).exponent = state.exponent := by
  simp [weightedBasis, sharedShift, sharedScale, threeBitBasis]

theorem weightedBasisResult_exponent (state : SharedDyadicState 3) (k j : Fin 8) :
    (weightedBasisResult state k).exponent = (weightedBasisResult state j).exponent := by
  exact replayExactNative_equal_exponents nativeToffoli012 (weightedBasis state k) (weightedBasis state j)
    (weightedBasisResult state k) (weightedBasisResult state j)
    (by rw [weightedBasis_exponent, weightedBasis_exponent]) (weightedBasis_replay state k) (weightedBasis_replay state j)

noncomputable def threeBitReplaySum (state : SharedDyadicState 3) : SharedDyadicState 3 :=
  sharedAddSame (weightedBasisResult state 0) (sharedAddSame (weightedBasisResult state 1)
  (sharedAddSame (weightedBasisResult state 2) (sharedAddSame (weightedBasisResult state 3)
  (sharedAddSame (weightedBasisResult state 4) (sharedAddSame (weightedBasisResult state 5)
  (sharedAddSame (weightedBasisResult state 6) (weightedBasisResult state 7)))))))

theorem sharedAddSame_exponent {n : Nat} (a b : SharedDyadicState n) :
    (sharedAddSame a b).exponent = a.exponent := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem toffoli_threeBit_replay_sum (state : SharedDyadicState 3) :
    replayExactNative 3 nativeToffoli012 state = some (threeBitReplaySum state) := by
  calc
    replayExactNative 3 nativeToffoli012 state = replayExactNative 3 nativeToffoli012 (threeBitDecomposition state) :=
      congrArg (replayExactNative 3 nativeToffoli012) (threeBitDecomposition_correct state).symm
    _ = some (threeBitReplaySum state) := by
      simp only [threeBitDecomposition, threeBitReplaySum, replayExactNative_add, weightedBasis_exponent,
        sharedAddSame_exponent, weightedBasis_replay, Option.bind_some, Option.map_some]

end SectorSimulation
