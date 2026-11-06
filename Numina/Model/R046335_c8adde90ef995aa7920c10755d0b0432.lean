import Mathlib

theorem algebra_597260 (a : ℝ) (h : a^5 - a^3 + a = 2) :
    3 < a^6 ∧ a^6 < 4 := by
  have h1 : a < 2 := by
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^2 - a), sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a^2 - 4), sq_nonneg (a^4 - 4)]
  have h2 : a > 1 := by
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^2 - a), sq_nonneg (a - 2), sq_nonneg (a + 2), sq_nonneg (a^2 - 4), sq_nonneg (a^4 - 4)]
  constructor
  · -- Show 3 < a^6.
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^2 - 2), sq_nonneg (a^2 - 3), sq_nonneg (a^2 - 4), sq_nonneg (a^6 - 3), sq_nonneg (a^3 - 2), mul_pos (show 0 < a - 1 by nlinarith) (show 0 < 2 - a by nlinarith)]
  · -- Show a^6 < 4.
    nlinarith [sq_nonneg (a^2 - 1), sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg (a^2 - 2), sq_nonneg (a^2 - 3), sq_nonneg (a^2 - 4), sq_nonneg (a^6 - 4), sq_nonneg (a^3 - 2), mul_pos (show 0 < a - 1 by nlinarith) (show 0 < 2 - a by nlinarith)]