import SectorSimulation.NativeCNOTReplay
namespace SectorSimulation

/-- Amplitudes indexed by computational-basis vectors; coefficients are arbitrary. -/
abbrev BasisAmplitudes (n : Nat) (A : Type) := BinaryVector n → A

/-- A CNOT permutes amplitude indices by its involutive basis action. -/
def applyCNOTAmplitude {n : Nat} {A : Type} (g : CNOTRecord n)
    (state : BasisAmplitudes n A) : BasisAmplitudes n A :=
  fun y => state (applyCNOT g.1 g.2 y)

def runCNOTAmplitudes {n : Nat} {A : Type} (gates : List (CNOTRecord n))
    (state : BasisAmplitudes n A) : BasisAmplitudes n A :=
  gates.foldl (fun s g => applyCNOTAmplitude g s) state

theorem runCNOTAmplitudes_apply {n : Nat} {A : Type} (gates : List (CNOTRecord n))
    (state : BasisAmplitudes n A) (y : BinaryVector n) :
    runCNOTAmplitudes gates state y = state (runCNOTs gates.reverse y) := by
  induction gates generalizing state with
  | nil => rfl
  | cons g rest ih =>
    simp only [runCNOTAmplitudes, List.foldl_cons]
    change runCNOTAmplitudes rest (applyCNOTAmplitude g state) y = _
    rw [ih]
    simp [applyCNOTAmplitude, List.reverse_cons, runCNOTs, List.foldl_append]

theorem gaussianCNOTAmplitude_action {n : Nat} {A : Type} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops)
    (state : BasisAmplitudes n A) (x : BinaryVector n) :
    runCNOTAmplitudes (rowProgramCNOTs ops).reverse state (matrixApply J x) = state x := by
  rw [runCNOTAmplitudes_apply, List.reverse_reverse]
  rw [gaussianCNOTs_forward_inverse J ops hprog x]

/-- Replay decoded native CNOT records on amplitude functions. -/
def replayCNOTAmplitudes {A : Type} (n : Nat) (gates : List NativeGate)
    (state : BasisAmplitudes n A) : Option (BasisAmplitudes n A) := do
  let decoded ← decodeCNOTProgram n gates
  if decoded.all (fun g => decide (g.1 ≠ g.2)) then
    some (runCNOTAmplitudes decoded state)
  else none

theorem replay_gaussian_CNOT_amplitudes {n : Nat} {A : Type} (J : BinaryMatrix n)
    (ops : List (RowOperation n)) (hprog : gaussianRowProgram J = some ops)
    (state : BasisAmplitudes n A) :
    ∃ result, replayCNOTAmplitudes n (encodeCNOTProgram (rowProgramCNOTs ops).reverse) state = some result ∧
      ∀ x, result (matrixApply J x) = state x := by
  have hv : validCNOTs (rowProgramCNOTs ops).reverse := by
    intro g hg
    exact rowProgramCNOTs_valid ops g (by simpa using hg)
  have hall : (rowProgramCNOTs ops).reverse.all (fun g => decide (g.1 ≠ g.2)) = true := by
    apply List.all_eq_true.mpr
    intro g hg
    exact decide_eq_true (hv g hg)
  refine ⟨runCNOTAmplitudes (rowProgramCNOTs ops).reverse state, ?_, ?_⟩
  · unfold replayCNOTAmplitudes
    rw [decode_encode_CNOTProgram]
    change (if (rowProgramCNOTs ops).reverse.all (fun g => decide (g.1 ≠ g.2)) then
      some (runCNOTAmplitudes (rowProgramCNOTs ops).reverse state) else none) = _
    rw [hall]
    rfl
  · intro x
    exact gaussianCNOTAmplitude_action J ops hprog state x

end SectorSimulation
