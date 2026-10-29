import SectorSimulation.ExactCubicPhase
import SectorSimulation.NativeGateHeader
namespace SectorSimulation

def sharedX {n : Nat} (wire : Fin n) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => state.numerator (flipWire wire x), state.exponent⟩

def sharedZ {n : Nat} (wire : Fin n) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => if x wire then cycloNeg (state.numerator x) else state.numerator x, state.exponent⟩

def sharedT {n : Nat} (wire : Fin n) (inverse : Bool) (state : SharedDyadicState n) : SharedDyadicState n :=
  ⟨fun x => if x wire then cycloMul (if inverse then cycloOmegaInv else cycloOmega) (state.numerator x)
    else state.numerator x, state.exponent⟩

/-- Executable exact shared-denominator action for the compiler gate alphabet. -/
def applyExactNative (n : Nat) (gate : NativeGate) (state : SharedDyadicState n) : Option (SharedDyadicState n) :=
  match gate with
  | ⟨"H", [wire]⟩ => if h : wire < n then some (sharedHadamard ⟨wire,h⟩ state) else none
  | ⟨"X", [wire]⟩ => if h : wire < n then some (sharedX ⟨wire,h⟩ state) else none
  | ⟨"Z", [wire]⟩ => if h : wire < n then some (sharedZ ⟨wire,h⟩ state) else none
  | ⟨"T", [wire]⟩ => if h : wire < n then some (sharedT ⟨wire,h⟩ false state) else none
  | ⟨"TDG", [wire]⟩ => if h : wire < n then some (sharedT ⟨wire,h⟩ true state) else none
  | ⟨"CX", [control,target]⟩ =>
    if hc : control < n then if ht : target < n then
      if control ≠ target then some (sharedCNOT ⟨control,hc⟩ ⟨target,ht⟩ state) else none
    else none else none
  | _ => none

def replayExactNative (n : Nat) : List NativeGate → SharedDyadicState n → Option (SharedDyadicState n)
  | [], state => some state
  | gate :: rest, state => do
    let next ← applyExactNative n gate state
    replayExactNative n rest next

theorem exactNative_HH {n : Nat} (wire : Fin n) (state : SharedDyadicState n) :
    replayExactNative n [⟨"H",[wire.val]⟩, ⟨"H",[wire.val]⟩] state =
      some (sharedHadamard wire (sharedHadamard wire state)) := by
  simp [replayExactNative, applyExactNative, wire.isLt]

theorem exactNative_HCXH {n : Nat} (control target : Fin n) (h : control ≠ target)
    (state : SharedDyadicState n) :
    replayExactNative n [⟨"H",[target.val]⟩, ⟨"CX",[control.val,target.val]⟩,
      ⟨"H",[target.val]⟩] state =
      some (sharedHadamard target (sharedCNOT control target (sharedHadamard target state))) := by
  have hv : control.val ≠ target.val := by
    intro he; exact h (Fin.ext he)
  simp [replayExactNative, applyExactNative, control.isLt, target.isLt, hv]

theorem exactNative_quadratic_phase {n : Nat} (control target : Fin n) (h : control ≠ target)
    (state : SharedDyadicState n) (x : BinaryVector n) :
    ∃ result, replayExactNative n [⟨"H",[target.val]⟩, ⟨"CX",[control.val,target.val]⟩,
      ⟨"H",[target.val]⟩] state = some result ∧
      sharedAmplitude result x = sharedAmplitude (sharedControlledSign control target state) x := by
  refine ⟨_, exactNative_HCXH control target h state, ?_⟩
  exact sharedHCXH_controlled_sign control target h state x

end SectorSimulation
