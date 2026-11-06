import Mathlib

theorem inequalities_198990 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b) / (1 + a + b) < a / (1 + a) + b / (1 + b) := by 
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + a + b := by linarith
  have h4 : (a + b) / (1 + a + b) - (a / (1 + a) + b / (1 + b)) < 0 := by
    have pos1 : 0 < (1 + a) * (1 + b) * (1 + a + b) := by
      positivity 
    have eq1 : (a + b) / (1 + a + b) - (a / (1 + a) + b / (1 + b)) = 
        ((a + b) * (1 + a) * (1 + b) - a * (1 + b) * (1 + a + b) - b * (1 + a) * (1 + a + b)) / ((1 + a) * (1 + b) * (1 + a + b)) := by 
      field_simp 
      ring 
    rw [eq1]
    have pos2 : (1 + a) * (1 + b) * (1 + a + b) > 0 := by positivity 
    have h5 : ((a + b) * (1 + a) * (1 + b) - a * (1 + b) * (1 + a + b) - b * (1 + a) * (1 + a + b)) < 0 := by 
      nlinarith [mul_pos ha hb, mul_pos ha h1, mul_pos hb h2, mul_pos ha h3, mul_pos hb h3]
    apply div_neg_of_neg_of_pos h5 pos2 
  linarith [h4]