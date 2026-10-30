import SectorSimulation.ColumnAction
namespace SectorSimulation

def safeColumnAdd {n : Nat} (J : BinaryMatrix n) (target source : Fin n) : BinaryMatrix n :=
  if target = source then J else columnAdd J target source

theorem columnAdd_involutive {n : Nat} (J : BinaryMatrix n) (target source : Fin n)
    (h : target ≠ source) : columnAdd (columnAdd J target source) target source = J := by
  funext i j
  by_cases hj : j = target
  · subst j
    simp only [columnAdd, if_pos rfl, if_neg (Ne.symm h)]
    cases J i target <;> cases J i source <;> rfl
  · simp [columnAdd, hj]

theorem safeColumnAdd_involutive {n : Nat} (J : BinaryMatrix n) (target source : Fin n) :
    safeColumnAdd (safeColumnAdd J target source) target source = J := by
  by_cases h : target = source
  · simp [safeColumnAdd, h]
  · simp [safeColumnAdd, h, columnAdd_involutive J target source h]

def runColumnAdds {n : Nat} (ops : List (Fin n × Fin n)) (J : BinaryMatrix n) : BinaryMatrix n :=
  ops.foldl (fun A op => safeColumnAdd A op.1 op.2) J

theorem runColumnAdds_reverse_cancels {n : Nat} (ops : List (Fin n × Fin n)) (J : BinaryMatrix n) :
    runColumnAdds ops.reverse (runColumnAdds ops J) = J := by
  induction ops generalizing J with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.reverse_cons, runColumnAdds, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change safeColumnAdd (runColumnAdds rest.reverse (runColumnAdds rest (safeColumnAdd J op.1 op.2))) op.1 op.2 = J
    rw [ih]
    exact safeColumnAdd_involutive J op.1 op.2

end SectorSimulation
