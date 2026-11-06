import Mathlib

theorem inequalities_1547 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (4 * a / (b + c) + 1) * (4 * b / (a + c) + 1) * (4 * c / (a + b) + 1) > 25 := by 
  have h1 : 0 < b + c := by
    linarith only [hb, hc]
  have h2 : 0 < a + c := by
    linarith only [ha, hc]
  have h3 : 0 < a + b := by
    linarith only [ha, hb]
  have h4 : (4 * a / (b + c) + 1) * (4 * b / (a + c) + 1) * (4 * c / (a + b) + 1) - 25 > 0 := by
    have h5 : (4 * a / (b + c) + 1) * (4 * b / (a + c) + 1) * (4 * c / (a + b) + 1) - 25 =
        ( (4 * a + b + c) * (4 * b + a + c) * (4 * c + a + b) - 25 * (b + c) * (a + c) * (a + b) ) / ( (b + c) * (a + c) * (a + b) ) := by
      field_simp
      ring
    rw [h5] at *
    have h6 : (4 * a + b + c) * (4 * b + a + c) * (4 * c + a + b) - 25 * (b + c) * (a + c) * (a + b) > 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a + b by linarith) (show 0 < a + c by linarith),
          mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith),
          mul_pos (show 0 < a + c by linarith) (show 0 < b + c by linarith)
          ]
    have h7 : ( (4 * a + b + c) * (4 * b + a + c) * (4 * c + a + b) - 25 * (b + c) * (a + c) * (a + b) ) / ( (b + c) * (a + c) * (a + b) ) > 0 := by
      apply div_pos
      linarith [ h6 ]
      all_goals
      positivity
    linarith [ h7 ]
  linarith [ h4 ]