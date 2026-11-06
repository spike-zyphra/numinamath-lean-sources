import Mathlib

theorem algebra_11235 {f : ℝ → ℝ} (h : ∀ x, x ≠ 1 / 3 → f x + f ((x + 1) / (1 - 3 * x)) = x) :
    f 2 = 48 / 35 := by
  have eq1 := h 2 (by norm_num)
  have eq2 := h (-3 / 5) (by norm_num)
  have eq3 := h (1 / 7) (by norm_num)
  norm_num at eq1 eq2 eq3
  linarith