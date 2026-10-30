import SectorSimulation.SourcePolarCertificate
import SectorSimulation.PivotComplete
namespace SectorSimulation

theorem safeColumnAdd_preserves_injective {n : Nat} (J : BinaryMatrix n) (t s : Fin n)
    (hJ : Function.Injective (matrixApply J)) :
    Function.Injective (matrixApply (safeColumnAdd J t s)) := by
  by_cases h : t = s
  · simpa [safeColumnAdd, h] using hJ
  · intro x y hxy
    simp only [safeColumnAdd, if_neg h, columnAdd_action] at hxy
    have he := hJ hxy
    have hs : s ≠ t := Ne.symm h
    have hi := congrArg (fun v => vectorAddRow v s t) he
    simpa [vectorAddRow_involutive, hs] using hi

theorem runColumnAdds_preserves_injective {n : Nat} (ops : List (Fin n × Fin n))
    (J : BinaryMatrix n) (hJ : Function.Injective (matrixApply J)) :
    Function.Injective (matrixApply (runColumnAdds ops J)) := by
  induction ops generalizing J with
  | nil => simpa [runColumnAdds] using hJ
  | cons op rest ih =>
    change Function.Injective (matrixApply (runColumnAdds rest (safeColumnAdd J op.1 op.2)))
    exact ih _ (safeColumnAdd_preserves_injective J op.1 op.2 hJ)

theorem polarEliminate_preserves_injective {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hJ : Function.Injective (matrixApply J)) :
    Function.Injective (matrixApply (polarEliminate B fuel indices J).1) := by
  rw [← polarEliminate_program B fuel indices J]
  exact runColumnAdds_preserves_injective _ J hJ

theorem polarEliminate_gaussian_program {n : Nat} (B : BinaryVector n → BinaryVector n → Bool)
    (fuel : Nat) (indices : List (Fin n)) (J : BinaryMatrix n)
    (hJ : Function.Injective (matrixApply J)) :
    ∃ ops, gaussianRowProgram (polarEliminate B fuel indices J).1 = some ops := by
  exact gaussianRowProgram_exists_of_injective _ (polarEliminate_preserves_injective B fuel indices J hJ)
end SectorSimulation
