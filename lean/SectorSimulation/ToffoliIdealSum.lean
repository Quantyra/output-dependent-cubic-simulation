import SectorSimulation.ToffoliSuperposition
namespace SectorSimulation

def idealWeightedBasis (state : SharedDyadicState 3) (k : Fin 8) : SharedDyadicState 3 :=
  sharedShift state.exponent (sharedScale (state.numerator (threeBitVector k)) (threeBitBasis (threeBitToffoliOutput k)))

def idealThreeBitSum (state : SharedDyadicState 3) : SharedDyadicState 3 :=
  sharedAddSame (idealWeightedBasis state 0) (sharedAddSame (idealWeightedBasis state 1)
  (sharedAddSame (idealWeightedBasis state 2) (sharedAddSame (idealWeightedBasis state 3)
  (sharedAddSame (idealWeightedBasis state 4) (sharedAddSame (idealWeightedBasis state 5)
  (sharedAddSame (idealWeightedBasis state 6) (idealWeightedBasis state 7)))))))

theorem idealWeightedBasis_exponent (state : SharedDyadicState 3) (k : Fin 8) :
    (idealWeightedBasis state k).exponent = state.exponent := by
  simp [idealWeightedBasis, sharedShift, sharedScale, threeBitBasis]

theorem weightedBasisResult_correct (state : SharedDyadicState 3) (k output : Fin 8) :
    sharedAmplitude (weightedBasisResult state k) (threeBitVector output) =
      sharedAmplitude (idealWeightedBasis state k) (threeBitVector output) := by
  obtain ⟨result, hr, he⟩ := toffoliScaledShiftedBasis_correct k output (state.numerator (threeBitVector k)) state.exponent
  have hr2 := weightedBasis_replay state k
  change replayExactNative 3 nativeToffoli012 (sharedShift state.exponent (sharedScale (state.numerator (threeBitVector k)) (threeBitBasis k))) = some _ at hr2
  rw [hr] at hr2
  have eq : result = weightedBasisResult state k := Option.some.inj hr2
  rw [← eq]
  exact he

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem toffoliReplaySum_amplitude (state : SharedDyadicState 3) (output : Fin 8) :
    sharedAmplitude (threeBitReplaySum state) (threeBitVector output) =
      sharedAmplitude (idealThreeBitSum state) (threeBitVector output) := by
  have he (k : Fin 8) : (weightedBasisResult state k).exponent = (weightedBasisResult state 0).exponent :=
    weightedBasisResult_exponent state k 0
  simp only [threeBitReplaySum, idealThreeBitSum, sharedAddSame_amplitude, sharedAddSame_exponent,
    he, idealWeightedBasis_exponent, weightedBasisResult_correct]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem idealThreeBitSum_correct (state : SharedDyadicState 3) (output : Fin 8) :
    sharedAmplitude (idealThreeBitSum state) (threeBitVector output) =
      sharedAmplitude (sharedToffoli 0 1 2 state) (threeBitVector output) := by
  have ho : output = 0 ∨ output = 1 ∨ output = 2 ∨ output = 3 ∨ output = 4 ∨ output = 5 ∨ output = 6 ∨ output = 7 := by
    have bound := output.isLt
    omega
  have h37 : flipWire 2 (threeBitVector 3) = threeBitVector 7 := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> decide
  have h73 : flipWire 2 (threeBitVector 7) = threeBitVector 3 := by
    funext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      have bound := i.isLt
      omega
    rcases hi with hi | hi | hi <;> subst i <;> decide
  rcases ho with h | h | h | h | h | h | h | h <;> subst output <;>
    simp (config := { decide := true }) [sharedAmplitude, idealThreeBitSum, idealWeightedBasis, sharedToffoli,
      sharedAddSame, sharedShift, sharedScale, threeBitBasis, threeBitVector, threeBitToffoliOutput,
      applyToffoli, h37, h73, List.finRange, Nat.testBit, cycloMul, cycloAdd, cycloOne]

theorem toffoli_threeBit_correct (state : SharedDyadicState 3) (output : Fin 8) :
    ∃ result, replayExactNative 3 nativeToffoli012 state = some result ∧
      sharedAmplitude result (threeBitVector output) =
        sharedAmplitude (sharedToffoli 0 1 2 state) (threeBitVector output) := by
  refine ⟨threeBitReplaySum state, toffoli_threeBit_replay_sum state, ?_⟩
  exact (toffoliReplaySum_amplitude state output).trans (idealThreeBitSum_correct state output)

end SectorSimulation
