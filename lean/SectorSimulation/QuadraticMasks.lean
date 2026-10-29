import SectorSimulation.CubicPhaseDerivative
import Batteries.Data.List.Lemmas

/-!
Semantic translation of individual quadratic terms into source bit masks.
The output degree bound and whole-list translation remain separate obligations.
-/

namespace SectorSimulation

def singletonMask {n : Nat} (i : Fin n) : Monomial n :=
  fun k => decide (k = i)

def pairMask {n : Nat} (i k : Fin n) : Monomial n :=
  fun t => decide (t = i ∨ t = k)

theorem evalMonomial_singletonMask {n : Nat} (i : Fin n) (x : BinaryVector n) :
    evalMonomial (singletonMask i) x = x i := by
  apply Bool.eq_iff_iff.mpr
  change (evalMonomial (singletonMask i) x = true ↔ x i = true)
  rw [evalMonomial_eq_true_iff]
  constructor
  · intro h
    exact h i (by simp [singletonMask])
  · intro hi k hk
    have same : k = i := by simpa [singletonMask] using hk
    subst k
    exact hi

theorem evalMonomial_pairMask {n : Nat} (i k : Fin n) (x : BinaryVector n) :
    evalMonomial (pairMask i k) x = (x i && x k) := by
  apply Bool.eq_iff_iff.mpr
  change (evalMonomial (pairMask i k) x = true ↔ (x i && x k) = true)
  rw [evalMonomial_eq_true_iff, Bool.and_eq_true_iff]
  constructor
  · intro h
    exact ⟨h i (by simp [pairMask]), h k (by simp [pairMask])⟩
  · intro h t ht
    have same : t = i ∨ t = k := by simpa [pairMask] using ht
    rcases same with rfl | rfl
    · exact h.1
    · exact h.2

def quadraticTermMask {n : Nat} (term : QuadraticTerm n) : Monomial n :=
  match term with
  | .constant => fun _ => false
  | .linear i => singletonMask i
  | .product i k => pairMask i k

/-- Every auxiliary quadratic term has the same value as its source bit mask. -/
theorem evalQuadraticTerm_mask {n : Nat} (term : QuadraticTerm n) (x : BinaryVector n) :
    evalMonomial (quadraticTermMask term) x = evalQuadraticTerm term x := by
  cases term with
  | constant => exact evalMonomial_emptyMask x
  | linear i => exact evalMonomial_singletonMask i x
  | product i k => exact evalMonomial_pairMask i k x

/-- Translate the auxiliary term list into the source's bit-mask ANF. -/
def quadraticTermsToANF {n : Nat} (terms : List (QuadraticTerm n)) : PhaseANF n :=
  terms.map quadraticTermMask

/-- The complete bit-mask translation preserves evaluation. -/
theorem evalQuadraticTerms_bitMasks {n : Nat} (terms : List (QuadraticTerm n))
    (x : BinaryVector n) :
    evalPhase (quadraticTermsToANF terms) x = evalQuadraticTerms terms x := by
  induction terms with
  | nil => rfl
  | cons term rest ih =>
    simp only [quadraticTermsToANF, List.map_cons, evalPhase_cons, evalQuadraticTerms]
    change evalPhase (List.map quadraticTermMask rest) x = evalQuadraticTerms rest x at ih
    rw [evalQuadraticTerm_mask, ih]


theorem two_choices_length {α : Type} (xs : List α) (a b : α)
    (hn : xs.Nodup) (hm : ∀ x ∈ xs, x = a ∨ x = b) : xs.length ≤ 2 := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys =>
      cases ys with
      | nil => simp
      | cons z zs =>
        simp only [List.nodup_cons, List.mem_cons] at hn
        have hx := hm x (by simp)
        have hy := hm y (by simp)
        have hz := hm z (by simp)
        grind

theorem pairMask_degree {n : Nat} (i k : Fin n) : monomialDegree (pairMask i k) ≤ 2 := by
  rw [monomialDegree_eq_selectedLength]
  apply two_choices_length _ i k
  · exact List.Nodup.sublist List.filter_sublist (List.nodup_finRange n)
  · intro x hx
    have h := (List.mem_filter.mp hx).2
    simpa [selectedVariables, pairMask] using h


end SectorSimulation
