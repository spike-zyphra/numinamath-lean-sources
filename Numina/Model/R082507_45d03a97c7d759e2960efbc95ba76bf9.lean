import Mathlib

theorem algebra_4786 {a b : ℝ} (h : ∀ x, (x + 1) * (x + 2) * (x + a) = x ^ 3 + b * x - 6) :
    b = -7 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h (-1)
  norm_num at eq1 eq2 eq3
  linarith