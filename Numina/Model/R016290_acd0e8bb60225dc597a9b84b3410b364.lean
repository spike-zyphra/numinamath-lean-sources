import Mathlib

theorem algebra_149479 (a : ℕ → ℝ) (h₀ : a 1 = 4) (h₁ : ∀ n, a (n + 1) = ∑ i in Finset.range n, a i + 2 * (n + 1) + 1) :
    a 1990 = 11 * 2 ^ 1988 - 2 := by
  have eq1 := h₁ 0
  norm_num [Finset.sum_range_zero] at eq1
  linarith [h₀, eq1]