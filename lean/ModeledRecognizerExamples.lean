import SectorSimulation.ModeledSourceRecognizer
open SectorSimulation

def exampleRecognizerBytes : List (Fin 256) := [91, 34, 99, 117, 98, 105, 99, 45, 102, 105, 101, 108, 100, 45, 118, 49, 34, 44, 49, 44, 91, 49, 93, 44, 91, 91, 93, 44, 91, 93, 93, 44, 48, 44, 48, 93]
def exampleRecognizerRaw : RawTwoPhaseDescriptor := ⟨1, [1], [], [], 0, 0⟩

def exampleRecognizedGates : List NativeGate :=
  match rawDescriptorToValidated exampleRecognizerRaw with
  | none => []
  | some ⟨_, d⟩ =>
    match gaussianRowProgram d.pairing with
    | none => []
    | some ops => encodeNumericHeader exampleRecognizerBytes ++ (compileModeledSourceBody d ops).getD []

#guard (recognizeModeledSource exampleRecognizedGates).isSome
#guard (recognizeModeledSource (exampleRecognizedGates ++ [⟨"X", [0]⟩])).isNone
#guard (recognizeModeledSource (encodeNumericHeader [255])).isNone
