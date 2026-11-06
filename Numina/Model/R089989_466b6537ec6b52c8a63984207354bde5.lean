import Mathlib

theorem inequalities_189956 (a b : ℝ) :
    (a + b)^4 ≤ 8 * (a^4 + b^4) := by
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 + b^2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b)]