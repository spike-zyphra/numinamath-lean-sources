import Mathlib

theorem inequalities_90811 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b + b / c + c / a ≥ (a + b) / (b + c) + (b + c) / (a + b) + 1 := by
  have h1 : 0 < a * b * c := by
    positivity
  have h3 : a / b + b / c + c / a - ((a + b) / (b + c) + (b + c) / (a + b) + 1) ≥ 0 := by
    have h4 : 0 < a * b * c * (b + c) * (a + b) := by
      positivity
    have h5 : a / b + b / c + c / a - ((a + b) / (b + c) + (b + c) / (a + b) + 1) =
        ( (a^2 * c * (a + b) * (b + c) + b^2 * a * (b + c) * (a + b) + c^2 * b * (a + b) * (b + c) - (a + b) * a * b * c * (a + b) - (b + c) * a * b * c * (b + c) - a * b * c * (b + c) * (a + b) ) / ( a * b * c * (b + c) * (a + b) ) ) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    have h6 : a^2 * c * (a + b) * (b + c) + b^2 * a * (b + c) * (a + b) + c^2 * b * (a + b) * (b + c) - (a + b) * a * b * c * (a + b) - (b + c) * a * b * c * (b + c) - a * b * c * (b + c) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < b + c by positivity) (show 0 < a + b by positivity), 
          mul_pos (show 0 < b + c by positivity) ha, 
          mul_pos (show 0 < a + b by positivity) hb, 
          mul_pos (show 0 < a + b by positivity) hc
          ]
    linarith
    all_goals
      positivity
  linarith