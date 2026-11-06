import Mathlib

theorem algebra_12053 {f : ℝ → ℝ} (h : ∀ x ≠ 0, 3 * f x - 2 * f (1 / x) = x) :
    f 4 = 5 / 2 := by
  have eq1 := h 4 (by norm_num)
  have eq2 := h (1 / 4) (by norm_num)
  norm_num at eq1 eq2
  linarith