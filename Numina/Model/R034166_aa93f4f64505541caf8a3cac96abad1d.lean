import Mathlib

theorem inequalities_97751 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
     (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) +
     (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2)) ≤ 8 := by
  have pos1 : 0 < 2 * a^2 + (b + c) ^ 2 := by positivity
  have pos2 : 0 < 2 * b^2 + (c + a) ^ 2 := by positivity
  have pos3 : 0 < 2 * c^2 + (a + b) ^ 2 := by positivity
  have h14 : ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
      (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) +
      (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) - 8) ≤ 0 := by
    have hx2 : ((2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
        (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) +
        (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2) - 8) = 
        (( (2 * a + b + c) ^ 2 ) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2 ) +
        ( (2 * b + c + a) ^ 2 ) * (2 * a^2 + (b + c) ^ 2) * (2 * c^2 + (a + b) ^ 2) +
        ( (2 * c + a + b) ^ 2 ) * (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) - 8 * ( (2 * a^2 + (b + c) ^ 2 ) * (2 * b^2 + (c + a) ^ 2 ) * (2 * c^2 + (a + b) ^ 2 ) ) 
      ) / ((2 * a^2 + (b + c)^2) * (2 * b^2 + (c + a)^2) * (2 * c^2 + (a + b)^2)) := by
      field_simp
      <;> ring
    rw [hx2] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is non-positive
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a * (a - b) ), sq_nonneg (a * (a - c) ), sq_nonneg (b * (b - c) ), 
          sq_nonneg (b * (b - a) ), sq_nonneg (c * (c - a) ), sq_nonneg (c * (c - b) ), 
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < a * c from by nlinarith), 
          mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith), 
          mul_pos (show 0 < a * c from by nlinarith) (show 0 < b * c from by nlinarith)
          ]
    · -- Show the denominator is non-negative
      positivity
  linarith