import Mathlib

theorem inequalities_601279 (a b c : ℝ) (h₀ : a^2 + b^2 + c^2 = 3) :
    a^3 * (b + c) + b^3 * (c + a) + c^3 * (a + b) ≤ 6 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b + c - 3), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]