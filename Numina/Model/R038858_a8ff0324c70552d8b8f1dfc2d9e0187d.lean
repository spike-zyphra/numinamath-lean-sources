import Mathlib

theorem inequalities_170103 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a * b * c * (a + b + c) ≤ a ^ 3 * b + b ^ 3 * c + c ^ 3 * a := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]