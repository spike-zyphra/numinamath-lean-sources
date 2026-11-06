import Mathlib

theorem algebra_15534 (a b c : ℝ) (h : ∀ x, -6 * x ^ 2 + 36 * x + 216 = a * (x + b) ^ 2 + c) :
    a + b + c = 261 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  ring_nf at eq1 eq2 eq3 eq4
  nlinarith [sq_nonneg (a + 6), sq_nonneg (b + 3), sq_nonneg (c - 270)]