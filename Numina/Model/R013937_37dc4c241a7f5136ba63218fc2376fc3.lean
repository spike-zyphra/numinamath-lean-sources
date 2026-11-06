import Mathlib

theorem inequalities_126204 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ 9 * a^2 * b^2 * c^2 := by 
  nlinarith [sq_nonneg (a^2 * b - b^2 * c), sq_nonneg (b^2 * c - c^2 * a), sq_nonneg (c^2 * a - a^2 * b),
          sq_nonneg (a * b^2 - b * c^2), sq_nonneg (b * c^2 - c * a^2), sq_nonneg (c * a^2 - a * b^2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc), 
          mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < c * a from mul_pos hc ha), 
          mul_pos (show 0 < b * c from mul_pos hb hc) (show 0 < c * a from mul_pos hc ha)]