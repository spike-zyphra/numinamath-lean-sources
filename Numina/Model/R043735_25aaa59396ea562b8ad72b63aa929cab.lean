import Mathlib

theorem inequalities_276771 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    25 < (1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) := by

  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith

  have h4 : (1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) =
      ((b + c + 4 * a) * (c + a + 4 * b) * (a + b + 4 * c)) / ((b + c) * (c + a) * (a + b)) := by
    field_simp
    <;> ring
  rw [h4] at *
  
  have h5 : ((b + c + 4 * a) * (c + a + 4 * b) * (a + b + 4 * c)) > 25 * ((b + c) * (c + a) * (a + b)) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos ha (show 0 < a + b by linarith), 
          mul_pos ha (show 0 < a + c by linarith), 
          mul_pos hb (show 0 < b + c by linarith), 
          mul_pos hb (show 0 < a + b by linarith), 
          mul_pos hc (show 0 < a + c by linarith), 
          mul_pos hc (show 0 < b + c by linarith)
          ]
  
  have h6 : ((b + c + 4 * a) * (c + a + 4 * b) * (a + b + 4 * c)) / ((b + c) * (c + a) * (a + b)) > 25 := by 
    apply (lt_div_iff₀ (by positivity)).mpr 
    nlinarith [h5]
  
  linarith [h6]
  all_goals 
    positivity