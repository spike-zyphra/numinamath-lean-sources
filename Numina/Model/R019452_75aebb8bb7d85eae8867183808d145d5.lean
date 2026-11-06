import Mathlib

theorem algebra_221067 (b c : ℝ) (h : ∃ x, -x^2 + b * x + c = x^2) :
    ∃ x, b * x + c = (1 / 2) * x^2 := by
  rcases h with ⟨x, hx⟩
  have hc : c = 2 * x^2 - b * x := by
    nlinarith
  use b + Real.sqrt (b^2 - 2 * b * x + 4 * x^2)
  rw [hc]
  nlinarith [Real.sqrt_nonneg (b^2 - 2 * b * x + 4 * x^2),
          Real.sq_sqrt (show (b^2 - 2 * b * x + 4 * x^2) ≥ 0 by nlinarith [sq_nonneg (b - x), sq_nonneg (x)])]