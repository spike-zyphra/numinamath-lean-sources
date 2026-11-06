import Mathlib

theorem inequalities_56854 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 3 / (a * b * c) ≥ a + b + c) :
    1 / a + 1 / b + 1 / c ≥ a + b + c := by
  have h1 : 0 < a * b * c := by
    positivity
  have h2 : 3 ≥ (a + b + c) * (a * b * c) := by
    have pos1 : a * b * c > 0 := h1
    have h3 : 3 / (a * b * c) ≥ a + b + c := h
    have h4 : (3 / (a * b * c) : ℝ) * (a * b * c) ≥ (a + b + c) * (a * b * c) := by
      apply mul_le_mul_of_nonneg_right
      linarith [h3]
      all_goals positivity
    have h5 : (3 / (a * b * c) : ℝ) * (a * b * c) = 3 := by
      field_simp [h1]
      all_goals linarith
    linarith [h4, h5, h1]
  have h3 : 1 / a + 1 / b + 1 / c - (a + b + c) ≥ 0 := by
    have h4 : 1 / a + 1 / b + 1 / c - (a + b + c) = ( (b * c + a * c + a * b) - (a + b + c) * (a * b * c) ) / (a * b * c) := by
      field_simp [show 0 < a * b * c by positivity]
      ring
    have h5 : ( (b * c + a * c + a * b) - (a + b + c) * (a * b * c) ) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (a * b - c * a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < a * c by nlinarith),
          pow_two_nonneg (a * b * c), 
          h2, pow_two_nonneg (a * b - b * c), pow_two_nonneg (b * c - c * a), pow_two_nonneg (a * b - c * a)
        ]
    have h6 : ( (b * c + a * c + a * b) - (a + b + c) * (a * b * c) ) / (a * b * c) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith [h4, h6]
  linarith [h3]