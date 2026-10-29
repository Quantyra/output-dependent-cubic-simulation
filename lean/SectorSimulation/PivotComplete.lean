import SectorSimulation.PivotExists
namespace SectorSimulation

theorem pivotSuffix_exists {n : Nat} (t : Nat) (ht : t ≤ n) (J : BinaryMatrix n)
    (hinj : ∀ x z, matrixApply J x = matrixApply J z → x = z)
    (hprior : ∀ k, k.val < t → ∀ r, J r k = decide (r = k)) :
    ∃ ops, pivotPrograms ((List.finRange n).drop t) J = some ops := by
  by_cases hlt : t < n
  · let p : Fin n := ⟨t, hlt⟩
    have hdrop : (List.finRange n).drop t = p :: (List.finRange n).drop (t+1) := by
      have hh := List.drop_eq_getElem_cons (l := List.finRange n) (i := t) (by simpa using hlt)
      simpa [p] using hh
    obtain ⟨row, hf⟩ := pivot_exists_of_injective J p hinj (by simpa [p] using hprior)
    let first := RowOperation.swap p row :: clearColumnOps (rowSwap J p row) p
    let next := (applyRowProgram first J zeroVector).1
    have hninj : ∀ x z, matrixApply next x = matrixApply next z → x = z :=
      rowProgram_preserves_injective first J zeroVector hinj
    have hnprior : ∀ k, k.val < t+1 → ∀ r, next r k = decide (r = k) := by
      intro k hk r
      by_cases he : k = p
      · subst k
        exact pivotStep_sets_unit J zeroVector p row hf r
      · have hklt : k.val < t := by
          have hv : k.val ≠ t := by intro hv; apply he; apply Fin.ext; simpa [p] using hv
          omega
        have hkeep := pivotStep_preserves_prior_unit J zeroVector k p row (by simpa [p] using hklt) hf (hprior k hklt) r
        exact hkeep.trans (hprior k hklt r)
    obtain ⟨tail, htail⟩ := pivotSuffix_exists (t+1) (by omega) next hninj hnprior
    refine ⟨first ++ tail, ?_⟩
    rw [hdrop]
    simp [pivotPrograms, hf, first, next, htail]
  · have heq : t = n := by omega
    subst t
    refine ⟨[], ?_⟩
    have hd : (List.finRange n).drop n = [] := List.drop_eq_nil_of_le (by simp)
    simp [hd, pivotPrograms]
termination_by n - t

theorem gaussianRowProgram_exists_of_injective {n : Nat} (J : BinaryMatrix n)
    (hinj : ∀ x z, matrixApply J x = matrixApply J z → x = z) :
    ∃ ops, gaussianRowProgram J = some ops := by
  obtain ⟨ops, h⟩ := pivotSuffix_exists 0 (Nat.zero_le n) J hinj (by intro k hk; omega)
  exact ⟨ops, by simpa [gaussianRowProgram] using h⟩

theorem gaussianSolveChecked_complete_of_injective {n : Nat} (J : BinaryMatrix n)
    (hinj : ∀ x z, matrixApply J x = matrixApply J z → x = z)
    (target : BinaryVector n) : ∃ x, gaussianSolveChecked J target = some x := by
  obtain ⟨ops, hop⟩ := gaussianRowProgram_exists_of_injective J hinj
  exact ⟨(applyRowProgram ops J target).2, gaussianSolveChecked_returns_of_program J ops hop target⟩

theorem gaussianRowProgram_success_iff_injective {n : Nat} (J : BinaryMatrix n) :
    (∃ ops, gaussianRowProgram J = some ops) ↔
      (∀ x z, matrixApply J x = matrixApply J z → x = z) := by
  constructor
  · rintro ⟨ops, hop⟩
    exact successfulProgram_injective J ops hop
  · exact gaussianRowProgram_exists_of_injective J

end SectorSimulation
