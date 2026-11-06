import Mathlib

theorem algebra_260880 (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = (x^2 - 100 * x + 196 + abs (x^2 - 100 * x + 196)) / 2) :
    ∑ i ∈ Finset.range 100, f (i + 1) = 390 := by
  norm_num [Finset.sum_range_succ, h₀]
  <;> norm_num [abs_of_nonneg, abs_of_nonpos, sq_nonneg]
  <;> norm_num