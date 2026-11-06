import Mathlib

theorem algebra_19914 {a b : ℝ} (h : ∀ x, x^2 - x - 1 = (x + a)^2 - b) :
    b = 5 / 4 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  nlinarith [sq_nonneg (a + 1 / 2)]