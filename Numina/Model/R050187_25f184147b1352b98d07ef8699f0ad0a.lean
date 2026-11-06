import Mathlib

theorem algebra_242656 (a : ℝ) (ha : a^5 - a^3 + a = 2) :
    3 < a^6 ∧ a^6 < 4 := by
  have h3 : 3 < a^6 := by
    nlinarith [sq_nonneg (a^3 - a), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^2 - 1), sq_nonneg (a^2), sq_nonneg (a * (a - 1)), sq_nonneg (a^2 * (a - 1)), sq_nonneg (a^3), sq_nonneg (a^4), sq_nonneg (a^5), sq_nonneg (a^6) ]
  have h4 : a^6 < 4 := by
    nlinarith [sq_nonneg (a^3 - a), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^2 - 1), sq_nonneg (a^2), sq_nonneg (a * (a - 1)), sq_nonneg (a^2 * (a - 1)), sq_nonneg (a^3), sq_nonneg (a^4), sq_nonneg (a^5), sq_nonneg (a^6) ]
  constructor
  · exact h3
  · exact h4