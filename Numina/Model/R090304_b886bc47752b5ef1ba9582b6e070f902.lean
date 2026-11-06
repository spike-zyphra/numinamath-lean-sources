import Mathlib

theorem inequalities_89297 (a : ℝ) (ha : a^5 - a^3 + a = 2) : 3 < a^6 ∧ a^6 < 4 := by
  have h1 : a > 0 := by
    nlinarith [sq_nonneg (a^2 - a + 1), sq_nonneg (a + 1), sq_nonneg (a - 1),
              sq_nonneg (a^2 - 1), sq_nonneg (a^2 - a), sq_nonneg (a^3 - 1),
              sq_nonneg (a^4 - a^2 + 1)]
  have h2 : 3 < a^6 := by
    nlinarith [sq_nonneg (a^2 - a + 1), sq_nonneg (a + 1), sq_nonneg (a - 1),
              sq_nonneg (a^2 - 1), sq_nonneg (a^2 - a), sq_nonneg (a^3 - 1),
              sq_nonneg (a^4 - a^2 + 1), sq_nonneg (a^2 - 2), sq_nonneg (a - 1)]
  have h3 : a^6 < 4 := by
    nlinarith [sq_nonneg (a^2 - a + 1), sq_nonneg (a + 1), sq_nonneg (a - 1),
              sq_nonneg (a^2 - 1), sq_nonneg (a^2 - a), sq_nonneg (a^3 - 1),
              sq_nonneg (a^4 - a^2 + 1), sq_nonneg (a^2 - 2), sq_nonneg (a - 1),
              sq_nonneg (a^3 - 1)]
  constructor
  · exact h2
  · exact h3