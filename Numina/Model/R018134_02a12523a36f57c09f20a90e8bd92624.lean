import Mathlib

theorem inequalities_326073
    (a b c d : ℝ)
    (h : (a + b + c)^2 ≥ 2 * (a^2 + b^2 + c^2) + 4 * d) :
    a * b + b * c + c * a ≥ 3 * d := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a + b + c - 3), sq_nonneg (a - b + c), sq_nonneg (a + b - c), sq_nonneg (-a + b + c)]