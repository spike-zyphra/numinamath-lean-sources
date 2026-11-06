import Mathlib

theorem inequalities_88095 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1 / 8) :
    a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 ≥ 15 / 16 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]