import Mathlib

theorem inequalities_199151 (a b : ℝ) :
    (a ^ 4 + a ^ 2 * b ^ 2 + b ^ 4) / 3 ≥ (a ^ 3 * b + b ^ 3 * a) / 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), sq_nonneg (a * (a + b)), sq_nonneg (b * (a + b)), sq_nonneg (a^2 - b^2), sq_nonneg (a * b), sq_nonneg ((a - b) * (a + b)), sq_nonneg (a * (a - b) - b * (a - b)), sq_nonneg (a^2 - 2*a*b + b^2), sq_nonneg (a^2 - 4*a*b + b^2), sq_nonneg ((a^2 - a*b) * (a^2 - a*b)), sq_nonneg ((a - 2*b) * (2*a - b)), sq_nonneg ((a - 2*b) * (a - 2*b)), sq_nonneg ((2*a - b) * (2*a - b))]