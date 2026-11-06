import Mathlib

theorem algebra_15813 (a b c d : ℝ) (h : ∀ x, (3 * x ^ 2 - 5 * x + 4) * (7 - 2 * x) = a * x ^ 3 + b * x ^ 2 + c * x + d) :
    8 * a + 4 * b + 2 * c + d = 18 := by
  have eq4 := h 2
  norm_num at eq4 ⊢
  linarith