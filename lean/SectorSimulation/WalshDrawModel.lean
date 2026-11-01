import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The finite-draw probability model: mean, variance and the signed readout

A draw variable is a real-valued function on a finite nonempty outcome type, and its mean is the
uniform average. This module proves the variance identity, the one-quarter variance bound for
`[0,1]`-valued draw variables, and the mean and variance of the signed readout `Y = 2 Z - 1` that
the manuscript's probability relation `p = (1 - E) / 2` uses.

What is not here: the paper's own equatorial draw variable, built from the sector states and the
Clifford observable. Its expectation is not proved, and neither is any concentration, median or
rounding step. This is the abstract bounded draw model, not the estimator theorem, and no
published theorem is certified.
-/

namespace SectorSimulation

open Finset

/-- The uniform mean of a real-valued function on a finite outcome type. -/
noncomputable def uniformMean {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card α : ℝ)

/-- The uniform variance of a real-valued function on a finite outcome type. -/
noncomputable def uniformVariance {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformMean (fun a => (f a - uniformMean f) ^ 2)

/-- The second moment of a real-valued function on a finite outcome type. -/
noncomputable def uniformSecondMoment {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  uniformMean (fun a => (f a) ^ 2)

/-- The signed readout `Y = 2 Z - 1` attached to a `[0,1]`-valued draw variable. -/
noncomputable def signedReadout {α : Type} (f : α → ℝ) : α → ℝ := fun a => 2 * f a - 1

variable {α : Type} [Fintype α] [Nonempty α]

/-- The outcome count is positive. -/
theorem card_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
  have h : 0 < Fintype.card α := Fintype.card_pos
  exact_mod_cast h

/-- A uniform mean of a nonnegative draw variable is nonnegative. -/
theorem uniformMean_nonneg (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  unfold uniformMean
  apply div_nonneg _ (le_of_lt card_pos)
  exact Finset.sum_nonneg (fun a _ => hf a)

/-- A uniform mean of a draw variable bounded by one is at most one. -/
theorem uniformMean_le_one (f : α → ℝ) (hf : ∀ a, f a ≤ 1) : uniformMean f ≤ 1 := by
  unfold uniformMean
  rw [div_le_one card_pos]
  calc ∑ a, f a ≤ ∑ _a : α, (1 : ℝ) := Finset.sum_le_sum (fun a _ => hf a)
    _ = (Fintype.card α : ℝ) := by simp

/-- A `[0,1]`-valued draw variable has mean in `[0,1]`. -/
theorem uniformMean_mem_unit (f : α → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    0 ≤ uniformMean f ∧ uniformMean f ≤ 1 :=
  ⟨uniformMean_nonneg f (fun a => (hf a).1), uniformMean_le_one f (fun a => (hf a).2)⟩

/-- For a `[0,1]`-valued draw variable the second moment is at most the mean. -/
theorem uniformSecondMoment_le_mean (f : α → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    uniformSecondMoment f ≤ uniformMean f := by
  unfold uniformSecondMoment uniformMean
  rw [div_le_div_iff_of_pos_right card_pos]
  refine Finset.sum_le_sum (fun a _ => ?_)
  have h1 := (hf a).1
  have h2 := (hf a).2
  nlinarith

/-- Expanding the squared deviation inside the finite sum. -/
theorem sum_sq_dev (f : α → ℝ) :
    (∑ a, (f a - uniformMean f) ^ 2)
      = (∑ a, (f a) ^ 2) - 2 * (uniformMean f) * (∑ a, f a)
        + (Fintype.card α : ℝ) * (uniformMean f) ^ 2 := by
  have hpt : ∀ a : α, (f a - uniformMean f) ^ 2
      = (f a) ^ 2 - 2 * (uniformMean f) * (f a) + (uniformMean f) ^ 2 := by
    intro a
    ring
  rw [Finset.sum_congr rfl (fun a _ => hpt a), Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The variance is the second moment minus the square of the mean. -/
theorem uniformVariance_eq (f : α → ℝ) :
    uniformVariance f = uniformSecondMoment f - (uniformMean f) ^ 2 := by
  have hC : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt card_pos
  unfold uniformVariance uniformSecondMoment uniformMean
  have hnum : (∑ a, (f a - (∑ b, f b) / (Fintype.card α : ℝ)) ^ 2)
      = (∑ a, (f a) ^ 2) - 2 * ((∑ b, f b) / (Fintype.card α : ℝ)) * (∑ a, f a)
        + (Fintype.card α : ℝ) * ((∑ b, f b) / (Fintype.card α : ℝ)) ^ 2 := by
    have h := sum_sq_dev f
    simpa [uniformMean] using h
  rw [hnum, add_div, sub_div]
  have h2 : 2 * ((∑ b, f b) / (Fintype.card α : ℝ)) * (∑ a, f a) / (Fintype.card α : ℝ)
      = 2 * (((∑ b, f b) / (Fintype.card α : ℝ)) * ((∑ a, f a) / (Fintype.card α : ℝ))) := by
    field_simp
  have h3 : (Fintype.card α : ℝ) * ((∑ b, f b) / (Fintype.card α : ℝ)) ^ 2
        / (Fintype.card α : ℝ)
      = ((∑ b, f b) / (Fintype.card α : ℝ)) ^ 2 := by
    field_simp
  rw [h2, h3]
  ring

/-- A `[0,1]`-valued draw variable has variance at most one quarter. -/
theorem uniformVariance_le_quarter (f : α → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    uniformVariance f ≤ 1 / 4 := by
  rw [uniformVariance_eq]
  have h2 := uniformSecondMoment_le_mean f hf
  have hμ := uniformMean_mem_unit f hf
  nlinarith [hμ.1, hμ.2, sq_nonneg (uniformMean f - 1 / 2)]

/-- The signed readout has mean twice the mean less one. -/
theorem uniformMean_signedReadout (f : α → ℝ) :
    uniformMean (signedReadout f) = 2 * uniformMean f - 1 := by
  unfold uniformMean signedReadout
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hC : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt card_pos
  field_simp

end SectorSimulation
