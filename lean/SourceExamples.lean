import SectorSimulation.BooleanSource

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
