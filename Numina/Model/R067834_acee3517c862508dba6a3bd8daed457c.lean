import Mathlib

theorem calculus_185715 (y1 y2 : ℝ → ℝ)
    (h1 : ∀ x, x^2 + y1 x^2 + 2 * x - 6 * y1 x + 2 = 0)
    (h2 : ∀ x, x^(y2 x) = (y2 x)^x) :
    deriv y1 1 = 1 ∧ deriv y2 1 = -1 := by
  have h1' := h1 2
  nlinarith [sq_nonneg (y1 2 - 3)]