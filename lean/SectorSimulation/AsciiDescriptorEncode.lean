import SectorSimulation.DescriptorJsonEncode
namespace SectorSimulation

def asciiBytes (chars : List (Fin 128)) : List (Fin 256) :=
  chars.map (fun c => ⟨c.val, Nat.lt_trans c.isLt (by decide)⟩)

def asciiText (chars : List (Fin 128)) : String :=
  String.ofList (chars.map (fun c => Char.ofNat c.val))

theorem asciiBytes_decode (chars : List (Fin 128)) :
    decodeAscii (asciiBytes chars) = some (asciiText chars) := by
  simp [decodeAscii, asciiBytes, asciiText, List.map_map, Function.comp_def]

theorem asciiSerializedValidDescriptor_has_recognizedBody
    (chars : List (Fin 128)) (raw : RawTwoPhaseDescriptor) (n : Nat) (d : CircuitDescriptor n)
    (hj : (Lean.Json.parse (asciiText chars)).toOption = some (rawDescriptorJson raw))
    (hv : rawDescriptorToValidated raw = some ⟨n, d⟩)
    (state : SharedDyadicState n) :
    ∃ ops body, recognizeModeledSource (encodeNumericHeader (asciiBytes chars) ++ body) = some ⟨n, (d, ops)⟩ := by
  exact serializedValidDescriptor_has_recognizedBody (asciiBytes chars) (asciiText chars) raw n d
    (asciiBytes_decode chars) hj hv state

end SectorSimulation
