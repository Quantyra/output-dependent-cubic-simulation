import SectorSimulation.NativeHeaderBits

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
