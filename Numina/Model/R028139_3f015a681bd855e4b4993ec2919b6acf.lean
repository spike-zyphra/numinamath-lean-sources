import Mathlib

theorem inequalities_598129 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + 2) * (b ^ 2 + 2) * (c ^ 2 + 2) ≥ 9 * (a * b + b * c + c * a) := by
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
    sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    sq_nonneg (a * b + b * c + c * a - 3),
    mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
  ]