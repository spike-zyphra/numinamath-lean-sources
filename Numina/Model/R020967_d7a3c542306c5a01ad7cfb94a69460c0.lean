import Mathlib

open Real

theorem inequalities_102347 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1 / 8) :
    a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ 15 / 16 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - 1 / 4), sq_nonneg (b * c - 1 / 4), sq_nonneg (c * a - 1 / 4),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]