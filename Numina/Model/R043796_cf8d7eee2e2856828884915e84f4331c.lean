import Mathlib

theorem inequalities_103104 {a b : ℝ} (h₀ : a^3 - b^3 = 2) (h₁ : a^5 - b^5 ≥ 4) :
    a^2 + b^2 ≥ 2 := by
  have h2 : a^2 + b^2 ≥ 2 * (a * b) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2 - 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - b^2), sq_nonneg (a * b), sq_nonneg (a^3 - b^3 - 2), sq_nonneg (a^5 - b^5 - 4), mul_nonneg (show 0 ≤ a^2 + b^2 by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - b^2), sq_nonneg (a * b)]) (show 0 ≤ (a - b) ^ 2 by nlinarith)]