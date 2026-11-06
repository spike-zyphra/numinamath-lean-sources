import Mathlib

theorem algebra_913 (a b c : ℝ) (h : ∀ x, (x^3 + a*x^2 + b*x + c) % (x^2 + 3*x - 4) = 0) : 2*a - 2*b - c = 14 := by
  have eq1 := h 1
  norm_num at eq1
  have eq2 := h (-4)
  norm_num at eq2
  have eq3 := h 0
  norm_num at eq3
  linarith