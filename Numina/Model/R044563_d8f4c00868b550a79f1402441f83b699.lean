import Mathlib

theorem inequalities_92391 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + c)^5 ≥ 81 * (a^2 + b^2 + c^2) * a * b * c := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)), 
          sq_nonneg (a * (a - c) + b * (b - c) + c * (c - a)), 
          sq_nonneg (a * (b - c) + b * (c - a) + c * (a - b)), 
          sq_nonneg (a^2 + b^2 + c^2 - a*b - b*c - c*a), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (mul_pos ha hb) hc, 
          mul_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (le_of_lt hc)]