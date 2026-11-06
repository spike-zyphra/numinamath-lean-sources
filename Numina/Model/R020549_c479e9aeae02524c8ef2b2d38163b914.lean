import Mathlib

theorem inequalities_4804 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b * c) / (b^2 + b * c + c^2) + (b^2 + c * a) / (c^2 + c * a + a^2) + (c^2 + a * b) / (a^2 + a * b + b^2) ≥ 2 := by
  have pos1 : 0 < b^2 + b * c + c^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have pos2 : 0 < c^2 + c * a + a^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have pos3 : 0 < a^2 + a * b + b^2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h3 : (a^2 + b * c) / (b^2 + b * c + c^2) + (b^2 + c * a) / (c^2 + c * a + a^2) + (c^2 + a * b) / (a^2 + a * b + b^2) - 2 ≥ 0 := by 
    have h4 : (a^2 + b * c) / (b^2 + b * c + c^2) + (b^2 + c * a) / (c^2 + c * a + a^2) + (c^2 + a * b) / (a^2 + a * b + b^2) - 2 =
        ((a^2 + b * c) * (c^2 + c * a + a^2) * (a^2 + a * b + b^2) 
        + (b^2 + c * a) * (b^2 + b * c + c^2) * (a^2 + a * b + b^2) 
        + (c^2 + a * b) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) 
        - 2 * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) * (a^2 + a * b + b^2)) / ((b^2 + b * c + c^2) * (c^2 + c * a + a^2) * (a^2 + a * b + b^2)) := by 
      field_simp 
      <;> ring
    rw [h4] 
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith), 
      mul_pos (show 0 < a * b from by nlinarith) (show 0 < c * a from by nlinarith), 
      mul_pos (show 0 < b * c from by nlinarith) (show 0 < c * a from by nlinarith)
      ]
    positivity
  linarith