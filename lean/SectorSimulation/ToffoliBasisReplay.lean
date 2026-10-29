import SectorSimulation.ExactNativeReplay
import SectorSimulation.ToffoliRecordTrace
namespace SectorSimulation

/-- Standard three-bit basis vector, with wire zero the low bit. -/
def threeBitVector (k : Fin 8) : BinaryVector 3 := fun i => k.val.testBit i.val

def threeBitBasis (k : Fin 8) : SharedDyadicState 3 :=
  ⟨fun x => if (List.finRange 3).all (fun i => x i == threeBitVector k i) then cycloOne else ⟨0,0,0,0⟩, 0⟩

def threeBitToffoliOutput (k : Fin 8) : Fin 8 :=
  if k.val.testBit 0 && k.val.testBit 1 then ⟨(k.val + 4) % 8, Nat.mod_lt _ (by decide)⟩ else k

/-- Exhaustively compare exact replay with ideal Toffoli on all three-bit basis inputs and outputs. -/
def toffoliBasisReplayCheck : Bool :=
  (List.finRange 8).all fun input =>
    match replayExactNative 3 nativeToffoli012 (threeBitBasis input) with
    | none => false
    | some result =>
      (List.finRange 8).all fun output =>
        let expected := threeBitBasis (threeBitToffoliOutput input)
        decide (cycloScale (2 ^ expected.exponent) (result.numerator (threeBitVector output)) =
          cycloScale (2 ^ result.exponent) (expected.numerator (threeBitVector output)))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem toffoliBasisReplayCheck_true : toffoliBasisReplayCheck = true := by decide

theorem toffoliBasisReplay_correct (input output : Fin 8) :
    ∃ result, replayExactNative 3 nativeToffoli012 (threeBitBasis input) = some result ∧
      sharedAmplitude result (threeBitVector output) =
        sharedAmplitude (threeBitBasis (threeBitToffoliOutput input)) (threeBitVector output) := by
  have hi := List.all_eq_true.mp toffoliBasisReplayCheck_true input (List.mem_finRange input)
  change (match replayExactNative 3 nativeToffoli012 (threeBitBasis input) with
    | none => false
    | some result => (List.finRange 8).all fun output =>
      let expected := threeBitBasis (threeBitToffoliOutput input)
      decide (cycloScale (2 ^ expected.exponent) (result.numerator (threeBitVector output)) =
        cycloScale (2 ^ result.exponent) (expected.numerator (threeBitVector output)))) = true at hi
  cases hr : replayExactNative 3 nativeToffoli012 (threeBitBasis input) with
  | none => simp [hr] at hi
  | some result =>
    refine ⟨result, rfl, ?_⟩
    simp only [hr] at hi
    have ho := List.all_eq_true.mp hi output (List.mem_finRange output)
    apply Quotient.sound
    change dyadicEquivalent ⟨result.numerator (threeBitVector output), result.exponent⟩
      ⟨(threeBitBasis (threeBitToffoliOutput input)).numerator (threeBitVector output),
        (threeBitBasis (threeBitToffoliOutput input)).exponent⟩
    unfold dyadicEquivalent
    exact of_decide_eq_true ho

end SectorSimulation
