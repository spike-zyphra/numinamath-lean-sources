import Mathlib

theorem algebra_250605 (b c : ℝ) (h : ∃ x, -x^2 + b * x + c = x^2) :
    ∃ x, (1 / 2) * x^2 + b * x + c = x^2 := by
  rcases h with ⟨x, hx⟩
  have h1 : (2) * x^2 - b * x - c = 0 := by
    nlinarith [hx]
  use b + Real.sqrt (b^2 + 2 * c)
  nlinarith [Real.sqrt_nonneg (b^2 + 2 * c), Real.sq_sqrt (show 0 ≤ (b^2 + 2 * c : ℝ) by
    nlinarith [sq_nonneg (x - b / 2), sq_nonneg (x), sq_nonneg (b + 2 * c), sq_nonneg (b * x)]
  )]