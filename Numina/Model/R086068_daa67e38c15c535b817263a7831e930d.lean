import Mathlib

theorem inequalities_28967 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c ≥ 1) :
    a^3 + b^3 + c^3 ≥ a * b + b * c + c * a := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc]