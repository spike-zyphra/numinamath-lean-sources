import Mathlib

theorem inequalities_602136 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^5 + b^5 + c^5 ≥ a^3 * b * c + b^3 * c * a + c^3 * a * b := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals assumption
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < a * c from mul_pos ha hc), 
          mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc), 
          mul_pos (show 0 < a * c from mul_pos ha hc) (show 0 < b * c from mul_pos hb hc), 
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos ha (show (0 : ℝ) < a * b from mul_pos ha hb),
          mul_pos hb (show (0 : ℝ) < a * b from mul_pos ha hb), 
          sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
          sq_nonneg (a * (a - c)), sq_nonneg (c * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (c * (b - c)), 
          pow_two_nonneg (a - b), pow_two_nonneg (a - c), pow_two_nonneg (b - c)
        ]