import SectorSimulation.NumericHeaderSound
import Lean.Data.Json
namespace SectorSimulation

structure RawTwoPhaseDescriptor where
  n : Nat
  rows : List Nat
  phase0 : List Nat
  phase1 : List Nat
  basis : Nat
  output : Nat
  deriving DecidableEq, Repr

def jsonNatList (j : Lean.Json) : Option (List Nat) := do
  let a ← j.getArr?.toOption
  a.toList.mapM (fun x => x.getNat?.toOption)

def extractTwoPhaseDescriptor (j : Lean.Json) : Option RawTwoPhaseDescriptor := do
  let root ← j.getArr?.toOption
  match root.toList with
  | [tag, width, rows, phases, basis, output] => do
    let version ← tag.getStr?.toOption
    if version != "cubic-field-v1" then none else do
      let n ← width.getNat?.toOption
      let rs ← jsonNatList rows
      let ps ← phases.getArr?.toOption
      match ps.toList with
      | [p0, p1] => do
        let f0 ← jsonNatList p0
        let f1 ← jsonNatList p1
        let b ← basis.getNat?.toOption
        let out ← output.getNat?.toOption
        some ⟨n, rs, f0, f1, b, out⟩
      | _ => none
  | _ => none

def decodeAscii (bytes : List (Fin 256)) : Option String :=
  if bytes.all (fun b => b.val < 128) then
    some (String.ofList (bytes.map fun b => Char.ofNat b.val))
  else none

def decodeHeaderDescriptor (gates : List NativeGate) : Option (RawTwoPhaseDescriptor × List NativeGate) := do
  let (bytes, body) ← decodeNumericHeader gates
  let text ← decodeAscii bytes
  let json ← (Lean.Json.parse text).toOption
  let desc ← extractTwoPhaseDescriptor json
  some (desc, body)

def rawMask {n : Nat} (m : Nat) : Monomial n := fun i => m.testBit i.val

def rawDescriptorToValidated (raw : RawTwoPhaseDescriptor) : Option (Σ n, CircuitDescriptor n) := do
  if raw.n = 0 then none else
  if raw.rows.length != raw.n then none else
  if !(raw.rows.all fun m => m < 2 ^ raw.n) then none else
  if !(raw.phase0.all fun m => m < 2 ^ raw.n) then none else
  if !(raw.phase1.all fun m => m < 2 ^ raw.n) then none else
  if raw.basis ≥ 2 ^ raw.n then none else
  if hout : raw.output < raw.n then
    let d : CircuitDescriptor raw.n :=
      ⟨(fun i k => (raw.rows.getD i.val 0).testBit k.val),
       raw.phase0.map rawMask, raw.phase1.map rawMask,
       (fun i => raw.basis.testBit i.val), ⟨raw.output, hout⟩⟩
    if sourceDescriptorValid d then some ⟨raw.n, d⟩ else none
  else none

def decodeValidatedHeader (gates : List NativeGate) : Option ((Σ n, CircuitDescriptor n) × List NativeGate) := do
  let (raw, body) ← decodeHeaderDescriptor gates
  let d ← rawDescriptorToValidated raw
  some (d, body)

theorem rawDescriptorToValidated_valid (raw : RawTwoPhaseDescriptor) (n : Nat)
    (d : CircuitDescriptor n) (h : rawDescriptorToValidated raw = some ⟨n, d⟩) :
    sourceDescriptorValid d = true := by
  unfold rawDescriptorToValidated at h
  repeat' split at h <;> simp_all
  rcases h with ⟨_, _, _, _, _, hout, hv, hn, hd⟩
  subst n
  cases hd
  exact hv

theorem decodeValidatedHeader_valid (gates : List NativeGate) (n : Nat)
    (d : CircuitDescriptor n) (body : List NativeGate)
    (h : decodeValidatedHeader gates = some (⟨n, d⟩, body)) :
    sourceDescriptorValid d = true := by
  unfold decodeValidatedHeader at h
  cases hr : decodeHeaderDescriptor gates with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨raw, suffix⟩
    cases hv : rawDescriptorToValidated raw with
    | none => simp [hr, hv] at h
    | some result =>
      cases result with
      | mk m candidate =>
        simp [hr, hv] at h
        obtain ⟨⟨hn, hd⟩, _⟩ := h
        subst n
        cases hd
        exact rawDescriptorToValidated_valid raw m candidate hv


end SectorSimulation
