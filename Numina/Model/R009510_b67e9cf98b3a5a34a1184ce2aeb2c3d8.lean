import Mathlib

theorem algebra_14318 {f : ℝ → ℝ} (h : ∀ x, f (3 * x - 1) = x ^ 2 + x + 1) : f 5 = 7 := by
  have eq1 := h 2
  norm_num at eq1
  linarith