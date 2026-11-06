import Mathlib

theorem algebra_5864 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ∀ x, (x + 1) * (x + 4) * (x + 9) = x^3 + a * x^2 + b * x + c) :
    a + b + c = 99 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  norm_num at eq1 eq2 eq3
  linarith