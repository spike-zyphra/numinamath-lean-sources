import Mathlib

theorem algebra_1322 {x : ℝ} (hx : x^5 - x^3 + x - 17 = 0) :
    4 < x^3 ∧ x^3 < 17 := by
  have h1 : 4 < x^3 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1), sq_nonneg (x^2 + 1),
      sq_nonneg (x^2 - x), sq_nonneg (x^2 + x),
      sq_nonneg (x^4 - 1), sq_nonneg (x^4 + 1),
      sq_nonneg (x^3 - 4), sq_nonneg (x^3 - 17)]
  have h2 : x^3 < 17 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^2 - 1), sq_nonneg (x^2 + 1),
      sq_nonneg (x^2 - x), sq_nonneg (x^2 + x),
      sq_nonneg (x^4 - 1), sq_nonneg (x^4 + 1),
      sq_nonneg (x^3 - 4), sq_nonneg (x^3 - 17)]
  constructor
  · exact h1
  · exact h2