import Mathlib

theorem inequalities_599700 (a b : ℝ) :
    ((a + b) / 2) * ((a ^ 2 + b ^ 2) / 2) * ((a ^ 3 + b ^ 3) / 2) ≤
    ((a ^ 6 + b ^ 6) / 2) := by
  nlinarith [sq_nonneg (a^3 - b^3), sq_nonneg (a^2 - b^2), sq_nonneg (a - b),
    sq_nonneg (a^3 + b^3), sq_nonneg (a^2 + b^2), sq_nonneg (a + b),
    sq_nonneg (a^2 - a*b), sq_nonneg (b^2 - a*b),
    sq_nonneg (a^2 + b^2 - a*b), sq_nonneg (a^2 + b^2 - 2*a*b)]