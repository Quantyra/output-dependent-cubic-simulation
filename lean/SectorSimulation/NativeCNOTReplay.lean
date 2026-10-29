import SectorSimulation.LinearCircuitCorrect
import SectorSimulation.NativeGateHeader
namespace SectorSimulation

def encodeCNOTRecord {n : Nat} (g : CNOTRecord n) : NativeGate :=
  ⟨"CX", [g.1.val, g.2.val]⟩

def decodeCNOTRecord (n : Nat) (gate : NativeGate) : Option (CNOTRecord n) :=
  match gate with
  | ⟨"CX", [control, target]⟩ =>
    if hc : control < n then
      if ht : target < n then some (⟨control, hc⟩, ⟨target, ht⟩) else none
    else none
  | _ => none

theorem decode_encode_CNOTRecord {n : Nat} (g : CNOTRecord n) :
    decodeCNOTRecord n (encodeCNOTRecord g) = some g := by
  rcases g with ⟨control, target⟩
  simp [decodeCNOTRecord, encodeCNOTRecord, control.isLt, target.isLt]

def encodeCNOTProgram {n : Nat} (gates : List (CNOTRecord n)) : List NativeGate :=
  gates.map encodeCNOTRecord

def decodeCNOTProgram (n : Nat) : List NativeGate → Option (List (CNOTRecord n))
  | [] => some []
  | gate :: rest => do
    let g ← decodeCNOTRecord n gate
    let gs ← decodeCNOTProgram n rest
    some (g :: gs)

theorem decode_encode_CNOTProgram {n : Nat} (gates : List (CNOTRecord n)) :
    decodeCNOTProgram n (encodeCNOTProgram gates) = some gates := by
  induction gates with
  | nil => rfl
  | cons g rest ih =>
    change decodeCNOTProgram n (List.map encodeCNOTRecord rest) = some rest at ih
    simp [decodeCNOTProgram, encodeCNOTProgram, decode_encode_CNOTRecord, ih]

def replayNativeCNOTs (n : Nat) (gates : List NativeGate) (x : BinaryVector n) :
    Option (BinaryVector n) := do
  let decoded ← decodeCNOTProgram n gates
  if decoded.all (fun g => decide (g.1 ≠ g.2)) then some (runCNOTs decoded x) else none

theorem replay_encoded_CNOTProgram {n : Nat} (gates : List (CNOTRecord n))
    (x : BinaryVector n) (hvalid : validCNOTs gates) :
    replayNativeCNOTs n (encodeCNOTProgram gates) x = some (runCNOTs gates x) := by
  have hall : gates.all (fun g => decide (g.1 ≠ g.2)) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    exact decide_eq_true (hvalid g hg)
  unfold replayNativeCNOTs
  rw [decode_encode_CNOTProgram]
  change (if gates.all (fun g => decide (g.1 ≠ g.2)) then some (runCNOTs gates x) else none) = _
  rw [hall]
  rfl

theorem replay_reversed_gaussian_CNOTs {n : Nat} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops)
    (x : BinaryVector n) :
    replayNativeCNOTs n (encodeCNOTProgram (rowProgramCNOTs ops).reverse) x = some (matrixApply J x) := by
  have hv : validCNOTs (rowProgramCNOTs ops).reverse := by
    intro gate hgate
    exact rowProgramCNOTs_valid ops gate (by simpa using hgate)
  rw [replay_encoded_CNOTProgram _ x hv, gaussianCNOTs_reversed_implements_matrix J ops hprog x]

end SectorSimulation
