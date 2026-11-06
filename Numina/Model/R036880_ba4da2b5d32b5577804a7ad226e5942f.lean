import Mathlib

theorem inequalities_596992 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((a / b + b / c + c / a) ^ 2 ≥ (a + b + c) * (1 / b + 1 / c + 1 / a)) := by

  have h1 : (a / b + b / c + c / a) ^ 2 - (a + b + c) * (1 / b + 1 / c + 1 / a) ≥ 0 := by
    have h2 : (a / b + b / c + c / a) ^ 2 - (a + b + c) * (1 / b + 1 / c + 1 / a) =
        ((a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) ^ 2 - (a + b + c) * (a * c + b * a + c * b) * (a * b * c)) / ( (a * b * c) ^ 2 ) := by
      field_simp 
      ring
    rw [h2] at *
    have h3 : ((a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) ^ 2 - (a + b + c) * (a * c + b * a + c * b) * (a * b * c)) ≥ 0 := by 
      have h11 : 0 < a * b * c := by positivity
      nlinarith [sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * a - c ^ 2 * b), sq_nonneg (c ^ 2 * b - a ^ 2 * c), 
          sq_nonneg (a * c - b * a), sq_nonneg (b * a - c * b), sq_nonneg (c * b - a * c), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < a * c by nlinarith)
        ]
    have h4 : (a * b * c) ^ 2 > 0 := by 
      positivity
    apply div_nonneg 
    linarith [h3]
    all_goals
      positivity 
  linarith