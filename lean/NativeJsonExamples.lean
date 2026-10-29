import SectorSimulation.NativeJsonDescriptor
open SectorSimulation

def headerExampleBytes : List (Fin 256) := [91, 34, 99, 117, 98, 105, 99, 45, 102, 105, 101, 108, 100, 45, 118, 49, 34, 44, 49, 44, 91, 49, 93, 44, 91, 91, 93, 44, 91, 93, 93, 44, 48, 44, 48, 93]
def expectedRaw : RawTwoPhaseDescriptor := ⟨1, [1], [], [], 0, 0⟩
#guard (Lean.Json.parse "[\"cubic-field-v1\",1,[1],[[],[]],0,0]").toOption.bind extractTwoPhaseDescriptor == some expectedRaw
#guard (rawDescriptorToValidated expectedRaw).isSome
#guard (rawDescriptorToValidated ⟨1, [0], [], [], 0, 0⟩).isNone
#guard (decodeValidatedHeader (encodeNumericHeader headerExampleBytes ++ [⟨"CX", [0, 1]⟩])).isSome
#guard (decodeValidatedHeader (encodeNumericHeader [255])).isNone
