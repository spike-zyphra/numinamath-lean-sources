import Mathlib

theorem algebra_51857 {f : ℝ → ℝ} (h : ∀ x, x ≠ 0 → 4 * f x + (2 / 3) * (x ^ 2 + 2) * f (x - 2 / x) = x ^ 3 + 1) : f 2 = 19 / 12 := by
  have eq1 := h 2 (by norm_num)
  have eq2 := h 1 (by norm_num)
  have eq3 := h (-1) (by norm_num)
  norm_num [show (2 : ℝ) - 2 / 2 = (1 : ℝ) by norm_num] at eq1
  norm_num [show (1 : ℝ) - 2 / 1 = (-1 : ℝ) by norm_num] at eq2
  norm_num [show (-1 : ℝ) - 2 / (-1) = (1 : ℝ) by norm_num] at eq3
  linarith