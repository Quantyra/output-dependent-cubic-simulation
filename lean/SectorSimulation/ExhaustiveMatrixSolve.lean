import SectorSimulation.MatrixLinearity
namespace SectorSimulation

def vectorCons {n : Nat} (b : Bool) (v : BinaryVector n) : BinaryVector (n+1) := Fin.cases b v
def vectorTail {n : Nat} (v : BinaryVector (n+1)) : BinaryVector n := fun i => v i.succ

def allVectors : (n : Nat) → List (BinaryVector n)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => (allVectors n).flatMap fun v => [vectorCons false v, vectorCons true v]

theorem allVectors_complete : ∀ {n : Nat} (v : BinaryVector n), v ∈ allVectors n := by
  intro n
  induction n with
  | zero =>
    intro v
    have h : v = (fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    simp [allVectors, h]
  | succ n ih =>
    intro v
    have h : vectorCons (v 0) (vectorTail v) = v := by
      funext i
      refine Fin.cases ?_ (fun k => ?_) i <;> simp [vectorCons, vectorTail]
    have hm := ih (vectorTail v)
    simp only [allVectors, List.mem_flatMap]
    refine ⟨vectorTail v, hm, ?_⟩
    cases hv : v 0 <;> simp_all

def vectorEqual {n : Nat} (x y : BinaryVector n) : Bool :=
  (List.finRange n).all fun i => x i == y i

theorem vectorEqual_correct {n : Nat} (x y : BinaryVector n) : vectorEqual x y = true ↔ x = y := by
  simp only [vectorEqual, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h; funext i; exact h i (List.mem_finRange i)
  · intro h i _; exact congrFun h i

def solveMatrixExhaustive {n : Nat} (J : BinaryMatrix n) (target : BinaryVector n) : Option (BinaryVector n) :=
  (allVectors n).find? fun v => vectorEqual (matrixApply J v) target

theorem solveMatrixExhaustive_sound {n : Nat} (J : BinaryMatrix n) (target v : BinaryVector n)
    (h : solveMatrixExhaustive J target = some v) : matrixApply J v = target := by
  apply (vectorEqual_correct _ _).mp
  exact List.find?_some (p := fun x => vectorEqual (matrixApply J x) target) h

theorem solveMatrixExhaustive_complete {n : Nat} (J : BinaryMatrix n) (target witness : BinaryVector n)
    (hw : matrixApply J witness = target) : ∃ v, solveMatrixExhaustive J target = some v := by
  cases h : solveMatrixExhaustive J target with
  | some v => exact ⟨v, rfl⟩
  | none =>
    have hn : ∀ x ∈ allVectors n, vectorEqual (matrixApply J x) target ≠ true := by
      simpa [solveMatrixExhaustive] using (List.find?_eq_none.mp h)
    have ht : vectorEqual (matrixApply J witness) target = true := (vectorEqual_correct _ _).mpr hw
    exact False.elim (hn witness (allVectors_complete witness) ht)

end SectorSimulation
