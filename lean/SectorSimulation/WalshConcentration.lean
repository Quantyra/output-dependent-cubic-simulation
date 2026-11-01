import SectorSimulation.WalshDrawModel

/-!
# Markov concentration on the finite draw model

`WalshDrawModel` supplies the uniform mean and variance of a draw variable on a finite outcome type.
This module adds the concentration ingredient the estimator argument uses: Markov's inequality on
the finite model, in counting form and in probability form.

The paper's estimate needs more than this — Chebyshev applied to the squared deviation, the median
argument over the independent groups, and the rounding and projection step. Those are not here.
In particular the paper's equatorial draw variable is not defined in the development, because the
sector states and the Clifford observable it is built from do not exist yet, so its expectation is
not proved and no published theorem is certified.
-/

namespace SectorSimulation

open Finset

variable {α : Type} [Fintype α] [Nonempty α]

/-- Markov's inequality in counting form: the outcomes where a nonnegative draw variable reaches
`ε` cost at least `ε` each in the total. -/
theorem markov_count (Z : α → ℝ) (hZ : ∀ a, 0 ≤ Z a) {ε : ℝ} (hε : 0 < ε) :
    (((Finset.univ.filter (fun a => ε ≤ Z a)).card : ℕ) : ℝ) * ε ≤ ∑ a, Z a := by
  have hconst : (((Finset.univ.filter (fun a => ε ≤ Z a)).card : ℕ) : ℝ) * ε
      = ∑ _a ∈ Finset.univ.filter (fun a => ε ≤ Z a), ε := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [hconst]
  calc ∑ _a ∈ Finset.univ.filter (fun a => ε ≤ Z a), ε
      ≤ ∑ a ∈ Finset.univ.filter (fun a => ε ≤ Z a), Z a :=
        Finset.sum_le_sum (fun a ha => (Finset.mem_filter.mp ha).2)
    _ ≤ ∑ a, Z a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun a _ _ => hZ a)

/-- Markov's inequality in probability form on the finite model. -/
theorem markov_prob (Z : α → ℝ) (hZ : ∀ a, 0 ≤ Z a) {ε : ℝ} (hε : 0 < ε) :
    ((((Finset.univ.filter (fun a => ε ≤ Z a)).card : ℕ) : ℝ)
        / (Fintype.card α : ℝ)) ≤ uniformMean Z / ε := by
  have hC : (0 : ℝ) < (Fintype.card α : ℝ) := card_pos
  have hden : (0 : ℝ) < (Fintype.card α : ℝ) * ε := mul_pos hC hε
  have h1 := markov_count (α := α) Z hZ hε
  have h2 : ((((Finset.univ.filter (fun a => ε ≤ Z a)).card : ℕ) : ℝ) * ε)
        / ((Fintype.card α : ℝ) * ε)
      = (((Finset.univ.filter (fun a => ε ≤ Z a)).card : ℕ) : ℝ) / (Fintype.card α : ℝ) := by
    field_simp
  have h3 : (∑ a, Z a) / ((Fintype.card α : ℝ) * ε) = uniformMean Z / ε := by
    unfold uniformMean
    field_simp
  calc ((((Finset.univ.filter (fun a => ε ≤ Z a)).card : ℕ) : ℝ)
        / (Fintype.card α : ℝ))
      = ((((Finset.univ.filter (fun a => ε ≤ Z a)).card : ℕ) : ℝ) * ε)
          / ((Fintype.card α : ℝ) * ε) := h2.symm
    _ ≤ (∑ a, Z a) / ((Fintype.card α : ℝ) * ε) :=
        div_le_div_iff_of_pos_right hden |>.mpr h1
    _ = uniformMean Z / ε := h3

end SectorSimulation
