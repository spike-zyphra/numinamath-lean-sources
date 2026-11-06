import Mathlib

theorem algebra_63907 {f : ℝ → ℝ} (h : ∀ x, 2 * f x + 3 * f (-x) = x ^ 2 + 5 * x) : f 7 = -126 / 5 := by
  have eq1 := h 7
  have eq2 := h (-7)
  norm_num at eq1 eq2 
  linarith