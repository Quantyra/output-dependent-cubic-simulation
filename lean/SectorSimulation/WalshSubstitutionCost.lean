import SectorSimulation.WalshCostComplete

/-!
# Refining the substitution stage: an exact phase-evaluation operation count

`WalshCostComplete` charges phase substitution as a modelling choice. This module refines that
stage's core computation from the executable program rather than from a specification: the phase
evaluator folds once per source monomial, and the fold's monomial count is proved exact and proved
to lie inside the model's substitution charge.

The count is carried by a counting wrapper around the existing evaluator, so the value component is
definitionally the existing evaluator's value. That is weaker than a merged instrumented loop, and
it is stated as such: the wrapper counts the monomial operations of the same fold shape, it does
not re-run an independent evaluator.

The other cost stages remain specifications, the estimator's accuracy statement is not proved here,
and no published theorem is certified.
-/

namespace SectorSimulation

/-- The phase evaluator with an exact operation count: the evaluator's value together with the
number of monomial operations of its fold. -/
def evalPhaseCosted {n : Nat} (p : PhaseANF n) (x : BinaryVector n) (init : Bool) : Bool × Nat :=
  (Bool.xor init (evalPhase p x), p.foldl (fun acc _ => acc + 1) 0)

/-- The counted value is the existing evaluator's value. -/
theorem evalPhaseCosted_fst {n : Nat} (p : PhaseANF n) (x : BinaryVector n) (init : Bool) :
    (evalPhaseCosted p x init).1 = Bool.xor init (evalPhase p x) := rfl

/-- Counting the monomial operations of the fold returns exactly the monomial count. -/
theorem foldl_monomialCount {n : Nat} (p : PhaseANF n) :
    p.foldl (fun acc (_ : Monomial n) => acc + 1) 0 = p.length := by
  have key : ∀ acc : Nat, p.foldl (fun acc (_ : Monomial n) => acc + 1) acc = acc + p.length := by
    intro acc
    induction p generalizing acc with
    | nil => simp
    | cons m rest ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        omega
  have h := key 0
  omega

/-- The instrumented evaluator spends exactly the monomial count. -/
theorem evalPhaseCosted_snd {n : Nat} (p : PhaseANF n) (x : BinaryVector n) (init : Bool) :
    (evalPhaseCosted p x init).2 = p.length :=
  foldl_monomialCount p

/-- The evaluated phase's operation count lies inside the model's substitution charge. -/
theorem evalPhaseCosted_ops_le {n : Nat} (p : PhaseANF n) (x : BinaryVector n) (init : Bool)
    (c : CostParameters) (hk : c.phaseCount = p.length) (hd : 1 ≤ c.dimension) :
    (evalPhaseCosted p x init).2 ≤ substitutionBitOps c := by
  rw [evalPhaseCosted_snd]
  rw [← hk]
  unfold substitutionBitOps
  rw [Nat.mul_assoc]
  have h1 : c.phaseCount ≤ c.phaseCount * c.dimension := by
    calc c.phaseCount = c.phaseCount * 1 := (Nat.mul_one _).symm
      _ ≤ c.phaseCount * c.dimension := Nat.mul_le_mul_left _ hd
  have h2 : c.phaseCount * c.dimension ≤ 2 * (c.phaseCount * c.dimension) := by
    calc c.phaseCount * c.dimension = 1 * (c.phaseCount * c.dimension) := (Nat.one_mul _).symm
      _ ≤ 2 * (c.phaseCount * c.dimension) := Nat.mul_le_mul_right _ (by omega : 1 ≤ 2)
  exact Nat.le_trans h1 h2

/-- The refined substitution stage is covered by the complete model total. -/
theorem substitution_refined_bitOps_le {n : Nat} (p : PhaseANF n) (x : BinaryVector n)
    (init : Bool) (c : CostParameters) (hk : c.phaseCount = p.length) (hd : 1 ≤ c.dimension) :
    (evalPhaseCosted p x init).2 ≤ totalBitOps c := by
  have h := evalPhaseCosted_ops_le p x init c hk hd
  unfold totalBitOps
  omega

end SectorSimulation
