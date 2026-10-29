import SectorSimulation.PhaseGateAmplitude
namespace SectorSimulation

/-- Decode and apply native X, Z and distinct-wire CX records to coefficient functions. -/
def applyNativeXZCNOT {A : Type} [Neg A] (n : Nat) (gate : NativeGate)
    (state : BasisAmplitudes n A) : Option (BasisAmplitudes n A) :=
  match gate with
  | ⟨"X", [wire]⟩ =>
      if h : wire < n then some (applyXAmplitude ⟨wire, h⟩ state) else none
  | ⟨"Z", [wire]⟩ =>
      if h : wire < n then some (applyZAmplitude ⟨wire, h⟩ state) else none
  | ⟨"CX", [control, target]⟩ =>
      if hc : control < n then
        if ht : target < n then
          if control ≠ target then
            some (applyCNOTAmplitude (⟨control, hc⟩, ⟨target, ht⟩) state)
          else none
        else none
      else none
  | _ => none

def replayNativeXZCNOT {A : Type} [Neg A] (n : Nat) :
    List NativeGate → BasisAmplitudes n A → Option (BasisAmplitudes n A)
  | [], state => some state
  | gate :: rest, state => do
      let next ← applyNativeXZCNOT n gate state
      replayNativeXZCNOT n rest next

theorem native_XZXZ_constant_phase {n : Nat} {A : Type} [Neg A]
    (wire : Fin n) (state : BasisAmplitudes n A) :
    replayNativeXZCNOT n [⟨"X", [wire.val]⟩, ⟨"Z", [wire.val]⟩,
      ⟨"X", [wire.val]⟩, ⟨"Z", [wire.val]⟩] state = some (fun x => -state x) := by
  simp [replayNativeXZCNOT, applyNativeXZCNOT, wire.isLt, XZXZ_constant_phase]

theorem native_Z_linear_phase {n : Nat} {A : Type} [Neg A]
    (wire : Fin n) (state : BasisAmplitudes n A) :
    replayNativeXZCNOT n [⟨"Z", [wire.val]⟩] state =
      some (fun x => if x wire then -state x else state x) := by
  simp [replayNativeXZCNOT, applyNativeXZCNOT, wire.isLt]
  rfl

theorem native_CNOT_step {n : Nat} {A : Type} [Neg A] (control target : Fin n)
    (h : control ≠ target) (state : BasisAmplitudes n A) :
    applyNativeXZCNOT n (encodeCNOTRecord (control, target)) state =
      some (applyCNOTAmplitude (control, target) state) := by
  have hv : control.val ≠ target.val := by
    intro he
    exact h (Fin.ext he)
  simp [applyNativeXZCNOT, encodeCNOTRecord, control.isLt, target.isLt, hv]

end SectorSimulation
