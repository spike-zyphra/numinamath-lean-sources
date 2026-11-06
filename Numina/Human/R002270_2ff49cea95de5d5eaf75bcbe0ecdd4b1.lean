import Mathlib
/-prove that  a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2) ≥ (a + b) * (a * b - 1)
for all positive real numbers a and b-/
theorem inequalities_80308 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 * b ^ 2 * (a ^ 2 + b ^ 2 - 2) ≥ (a + b) * (a * b - 1) := by
  nlinarith [sq_nonneg (a * b * a - 1), sq_nonneg (a * b * b - 1), sq_nonneg (a - b),
    sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1),
    mul_pos ha hb, mul_pos ha (show 0 < b by linarith), mul_pos (show 0 < a by linarith) hb,
    sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (a * b - 1),
    sq_nonneg (a - b), sq_nonneg (a * b * a - 1), sq_nonneg (a * b * b - 1)]