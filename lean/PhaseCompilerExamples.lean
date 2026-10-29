import SectorSimulation.PhaseBlockCompiler
open SectorSimulation

def exampleMask4 (i : Fin 4) : Monomial 4 := fun j => decide (j = i)
def exampleAll4 : Monomial 4 := fun _ => true

def exampleTriple : Monomial 4 := fun j => decide (j = 0 ∨ j = 1 ∨ j = 2)

example : (compilePhaseRecords (0 : Fin 4) [exampleMask4 1, exampleTriple]).isSome = true := by decide
example : compilePhaseRecords (0 : Fin 4) [exampleAll4] = none := by decide
example : (compilePhaseRecords (0 : Fin 4) []).isSome = true := by decide
