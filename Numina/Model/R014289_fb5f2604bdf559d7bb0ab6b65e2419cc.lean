import Mathlib

theorem inequalities_601330 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) +
    3 * (a * b + b * c + c * a) / (a + b + c)^2 ≥ 4 := by 
  have h4 : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c)^2 - 4 ≥ 0 := by
    have hx1 : 0 < (b + c) := by positivity
    have hx2 : 0 < (c + a) := by positivity
    have hx3 : 0 < (a + b) := by positivity
    have hx4 : 0 < (b + c) * (c + a) * (a + b) * (a + b + c) ^ 2 := by positivity
    have h5 : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) + 3 * (a * b + b * c + c * a) / (a + b + c)^2 - 4 =
      ( ((a + b) * (c + a) * (a + b) * (a + b + c) ^ 2) +
          ((b + c) * (b + c) * (a + b) * (a + b + c) ^ 2) +
            ((c + a) * (b + c) * (c + a) * (a + b + c) ^ 2) +
            (3 * (a * b + b * c + c * a) * (b + c) * (c + a) * (a + b)) - 4 * ((b + c) * (c + a) * (a + b) * (a + b + c) ^ 2) )
            / ((b + c) * (c + a) * (a + b) * (a + b + c) ^ 2) := by 
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < b * c from mul_pos hb hc), 
      mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < a * c from mul_pos ha hc), 
      mul_pos (show 0 < b * c from mul_pos hb hc) (show 0 < a * c from mul_pos ha hc), 
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)
    ]
    all_goals
      positivity
  linarith