import SectorSimulation.ExactNativeReplay
open SectorSimulation

def exampleState : SharedDyadicState 1 := ⟨fun _ => cycloOne, 0⟩

#guard (replayExactNative 1 [⟨"CX", [0,0]⟩] exampleState).isNone
#guard (replayExactNative 1 [⟨"H", [1]⟩] exampleState).isNone
#guard (replayExactNative 1 [⟨"unknown", [0]⟩] exampleState).isNone
#guard (replayExactNative 1 [⟨"H", [0]⟩, ⟨"H", [0]⟩] exampleState).isSome
