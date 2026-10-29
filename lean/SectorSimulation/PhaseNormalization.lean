import SectorSimulation.BooleanSource
namespace SectorSimulation

/-- Reordering an ANF list does not change the Boolean polynomial it denotes. -/
theorem evalPhase_perm {n : Nat} {p q : PhaseANF n} (h : p.Perm q) (x : BinaryVector n) :
    evalPhase p x = evalPhase q x := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [evalPhase_cons, ih]
  | swap a b tail =>
    simp only [evalPhase_cons]
    cases evalMonomial a x <;> cases evalMonomial b x <;> cases evalPhase tail x <;> rfl
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- Two occurrences of the same mask can be removed even when separated. -/
theorem evalPhase_cancel_separated {n : Nat} (left mid right : PhaseANF n)
    (m : Monomial n) (x : BinaryVector n) :
    evalPhase (left ++ [m] ++ mid ++ [m] ++ right) x =
      evalPhase (left ++ mid ++ right) x := by
  simp only [evalPhase_append, evalPhase_cons, evalPhase_empty]
  cases evalPhase left x <;> cases evalPhase mid x <;> cases evalPhase right x <;>
    cases evalMonomial m x <;> rfl

end SectorSimulation
