import SectorSimulation.NumericHeaderBytes

open SectorSimulation

/- Finite sanity checks for constant terms, selected variables and duplicate
   cancellation. They test the representation; they are not the general
   native-source or circuit-denotation theorem. -/
example : evalMonomial (fun _ => false : Monomial 2) (fun _ => false) = true := by
  decide

example : evalPhase (n := 2) [fun i => i.val == 0] (fun i => i.val == 0) = true := by
  decide

example : evalPhase (n := 2) [fun i => i.val == 0] (fun _ => false) = false := by
  decide

example : evalPhase (n := 2) [fun i => i.val == 0, fun i => i.val == 0]
    (fun i => i.val == 0) = false := by
  decide


def validDescriptor : CircuitDescriptor 2 :=
  ⟨(fun i k => decide (i = k)), [], [], (fun _ => false), 0⟩

def singularDescriptor : CircuitDescriptor 2 :=
  ⟨(fun _ _ => false), [], [], (fun _ => false), 0⟩

def asymmetricDescriptor : CircuitDescriptor 2 :=
  ⟨(fun i k => decide (i = k ∨ (i.val = 0 ∧ k.val = 1))), [], [], (fun _ => false), 0⟩

#guard sourceDescriptorValid validDescriptor
#guard !sourceDescriptorValid singularDescriptor
#guard !sourceDescriptorValid asymmetricDescriptor


#guard decodeHeaderBits [.x0, .x0, .z0, .z0, .h0, .h0, .other] == some ([false, true], [.other])
#guard (decodeHeaderBits [.x0, .z0, .h0, .h0]).isNone
#guard (decodeHeaderBits [.x0, .x0]).isNone


#guard decodeNativeHeader (encodeNativeHeader [false, true] ++ [⟨"CX", [2, 1]⟩]) == some ([false, true], [⟨"CX", [2, 1]⟩])
#guard (decodeNativeHeader [⟨"X", [1]⟩, ⟨"X", [1]⟩, nativeH0, nativeH0]).isNone
#guard (decodeNativeHeader [nativeX0, nativeZ0, nativeH0, nativeH0]).isNone


def headerByteA : HeaderByte := ⟨false, true, false, false, false, false, false, true⟩
#guard decodeNativeByteHeader (encodeNativeByteHeader [headerByteA] ++ [⟨"CX", [2, 1]⟩]) == some ([headerByteA], [⟨"CX", [2, 1]⟩])
#guard (decodeNativeByteHeader (encodeNativeHeader [true])).isNone

#guard headerByteValue headerByteA == 65
#guard decodeNumericHeader (encodeNumericHeader [65, 255] ++ [⟨"CX", [2, 1]⟩]) == some ([65, 255], [⟨"CX", [2, 1]⟩])
