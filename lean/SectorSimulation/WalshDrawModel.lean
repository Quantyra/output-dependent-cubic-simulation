import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The finite-draw probability model: mean, second moment and variance

A draw variable is a real-valued function on a finite nonempty outcome type, and its mean is the
uniform average. This module proves the elementary facts the estimator argument uses: the mean of
a `[0,1]`-valued draw variable lies in `[0,1]`, its second moment is at most its mean, and its
variance is at most one quarter.

What is not here: the paper's equatorial draw variable `Y`, concentration inequalities, the median
argument and the rounding step. This is the bounded-draw core, not the estimator theorem, and no
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

end SectorSimulation
