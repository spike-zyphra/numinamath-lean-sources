import Mathlib

theorem algebra_191015 : ¬∃ x : ℝ, x^4 - 6 * x^3 + 14 * x^2 - 24 * x + 40 = 0 := by 
  rintro ⟨x, hx⟩
  have h1 : x^4 - 6 * x^3 + 14 * x^2 - 24 * x + 40 > (0 : ℝ) := by
    nlinarith [sq_nonneg (x^2 - 3 * x + 2), sq_nonneg (x - 3), sq_nonneg (x^2), sq_nonneg (x), sq_nonneg (x - 4), sq_nonneg (x - 2)]
  nlinarith