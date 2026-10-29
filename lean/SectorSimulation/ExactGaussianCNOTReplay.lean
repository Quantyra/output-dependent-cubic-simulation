import SectorSimulation.SourcePhaseCompiler
namespace SectorSimulation

def runSharedCNOTs {n : Nat} (gates : List (CNOTRecord n)) (state : SharedDyadicState n) : SharedDyadicState n :=
  gates.foldl (fun s g => sharedCNOT g.1 g.2 s) state

theorem runSharedCNOTs_numerator {n : Nat} (gates : List (CNOTRecord n))
    (state : SharedDyadicState n) (x : BinaryVector n) :
    (runSharedCNOTs gates state).numerator x = runCNOTAmplitudes gates state.numerator x := by
  induction gates generalizing state with
  | nil => rfl
  | cons g rest ih =>
    simpa [runSharedCNOTs, runCNOTAmplitudes, sharedCNOT, applyCNOTAmplitude] using ih (sharedCNOT g.1 g.2 state)

theorem runSharedCNOTs_exponent {n : Nat} (gates : List (CNOTRecord n))
    (state : SharedDyadicState n) : (runSharedCNOTs gates state).exponent = state.exponent := by
  induction gates generalizing state with
  | nil => rfl
  | cons g rest ih => simpa [runSharedCNOTs, sharedCNOT] using ih (sharedCNOT g.1 g.2 state)

theorem exactNativeCNOTProgram {n : Nat} (gates : List (CNOTRecord n))
    (valid : validCNOTs gates) (state : SharedDyadicState n) :
    replayExactNative n (encodeCNOTProgram gates) state = some (runSharedCNOTs gates state) := by
  induction gates generalizing state with
  | nil => rfl
  | cons g rest ih =>
    have hg : g.1 ≠ g.2 := valid g (by simp)
    have hr : validCNOTs rest := by intro r hm; exact valid r (by simp [hm])
    have hv : g.1.val ≠ g.2.val := by intro he; exact hg (Fin.ext he)
    simp only [encodeCNOTProgram, List.map_cons, replayExactNative, encodeCNOTRecord, applyExactNative,
      g.1.isLt, g.2.isLt, hv, dif_pos, if_false, runSharedCNOTs, List.foldl_cons]
    simpa [hv, encodeCNOTProgram, runSharedCNOTs] using ih hr (sharedCNOT g.1 g.2 state)

theorem exactNativeGaussianCNOTs {n : Nat} (J : BinaryMatrix n) (ops : List (RowOperation n))
    (hprog : gaussianRowProgram J = some ops) (state : SharedDyadicState n) :
    ∃ result, replayExactNative n (encodeCNOTProgram (rowProgramCNOTs ops).reverse) state = some result ∧
      ∀ x, sharedAmplitude result (matrixApply J x) = sharedAmplitude state x := by
  have hv : validCNOTs (rowProgramCNOTs ops).reverse := by
    intro g hg; exact rowProgramCNOTs_valid ops g (by simpa using hg)
  refine ⟨runSharedCNOTs (rowProgramCNOTs ops).reverse state, exactNativeCNOTProgram _ hv state, ?_⟩
  intro x
  simp only [sharedAmplitude, runSharedCNOTs_numerator, runSharedCNOTs_exponent]
  rw [gaussianCNOTAmplitude_action J ops hprog state.numerator x]

end SectorSimulation
