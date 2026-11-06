import Mathlib

theorem inequalities_233691 (a b c : ℝ) (h : a * b * c = 1) :
    a ^ 4 + b ^ 4 + c ^ 4 ≥ a + b + c := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a + b + c - 3), sq_nonneg (a * b + b * c + c * a - 3),
    mul_self_nonneg (a * b - 1), mul_self_nonneg (b * c - 1), mul_self_nonneg (c * a - 1)]