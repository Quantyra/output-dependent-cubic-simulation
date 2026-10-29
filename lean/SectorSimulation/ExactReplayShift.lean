import SectorSimulation.CycloAssociativity
import SectorSimulation.ToffoliBasisReplay
namespace SectorSimulation

def sharedShift {n : Nat} (d : Nat) (state : SharedDyadicState n) : SharedDyadicState n :=
  { numerator := state.numerator, exponent := state.exponent + d }

theorem applyExactNative_shift {n : Nat} (gate : NativeGate) (d : Nat) (state : SharedDyadicState n) :
    applyExactNative n gate (sharedShift d state) =
      (applyExactNative n gate state).map (sharedShift d) := by
  unfold applyExactNative
  repeat' split <;> simp_all [sharedShift, sharedHadamard, sharedX, sharedZ, sharedT, sharedCNOT, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals split <;> try simp_all [sharedShift, sharedCNOT]
  all_goals split <;> try simp_all [sharedShift, sharedCNOT]
  all_goals split <;> try simp_all [sharedShift, sharedCNOT]

  all_goals omega

theorem replayExactNative_shift {n : Nat} (gates : List NativeGate) (d : Nat) (state : SharedDyadicState n) :
    replayExactNative n gates (sharedShift d state) =
      (replayExactNative n gates state).map (sharedShift d) := by
  induction gates generalizing state with
  | nil => rfl
  | cons gate rest ih =>
    cases h : applyExactNative n gate state with
    | none =>
      have hs : applyExactNative n gate (sharedShift d state) = none := by
        rw [applyExactNative_shift gate d state, h]
        rfl
      simp [replayExactNative, h, hs]
    | some next =>
      have hs : applyExactNative n gate (sharedShift d state) = some (sharedShift d next) := by
        rw [applyExactNative_shift gate d state, h]
        rfl
      simpa [replayExactNative, h, hs] using ih next

theorem toffoliScaledShiftedBasis_replay (input output : Fin 8) (k : Cyclo8) (d : Nat) :
    ∃ result, replayExactNative 3 nativeToffoli012 (sharedShift d (sharedScale k (threeBitBasis input))) =
      some (sharedShift d (sharedScale k result)) ∧
      sharedAmplitude result (threeBitVector output) =
        sharedAmplitude (threeBitBasis (threeBitToffoliOutput input)) (threeBitVector output) := by
  obtain ⟨result, hr, he⟩ := toffoliBasisReplay_correct input output
  refine ⟨result, ?_, he⟩
  rw [replayExactNative_shift, replayExactNative_scale, hr]
  rfl

end SectorSimulation
