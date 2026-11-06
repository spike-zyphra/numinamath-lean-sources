import Mathlib

theorem inequalities_177758 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < a + c := by linarith
  have h3 : 0 < a + b := by linarith
  
  have h4 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by

    have pos1 : 0 < (b + c) * (a + c) * (a + b) := by
      positivity

    have h5 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
          (2 * a * (a + c) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (a + c) - 3 * (b + c) * (a + c) * (a + b)) / (2 * (b + c) * (a + c) * (a + b)) := by 
      field_simp
      ring

    rw [h5]

    apply div_nonneg
    -- Show numerator is non-negative 
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show (0 : ℝ) < a + b by linarith) (show (0 : ℝ) < a + c by linarith), 
          mul_pos (show (0 : ℝ) < a + b by linarith) (show (0 : ℝ) < b + c by linarith), 
          mul_pos (show (0 : ℝ) < a + c by linarith) (show (0 : ℝ) < b + c by linarith)
          ]
    -- show denominator is non-negative 
    positivity
  
  linarith