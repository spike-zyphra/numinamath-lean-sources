import Mathlib

theorem inequalities_8645 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a * b / (a + b) + c * d / (c + d) ≤ (a + c) * (b + d) / (a + b + c + d) := by
  have h1 : 0 < a + b := by linarith 
  have h2 : 0 < c + d := by linarith 
  have h3 : 0 < a + b + c + d := by linarith 
  have h4 : a * b / (a + b) + c * d / (c + d) - (a + c) * (b + d) / (a + b + c + d) ≤ 0 := by
    have numerator_le_zero : a * b * (c + d) * (a + b + c + d) + c * d * (a + b) * (a + b + c + d) - (a + c) * (b + d) * (a + b) * (c + d) ≤ 0 := by 
      nlinarith [sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c), sq_nonneg (a * d - c * b), sq_nonneg (a - c), sq_nonneg (b - d), sq_nonneg (a * c - b * c), sq_nonneg (a * b - c * d), sq_nonneg (a + c - (b + d)), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
    have h6 : 0 < (a + b) * (c + d) * (a + b + c + d) := by positivity
    have h7 : a * b / (a + b) + c * d / (c + d) - (a + c) * (b + d) / (a + b + c + d) 
      = (a * b * (c + d) * (a + b + c + d) + c * d * (a + b) * (a + b + c + d) - (a + c) * (b + d) * (a + b) * (c + d)) / ((a + b) * (c + d) * (a + b + c + d)) := by 
      field_simp
      ring
    rw [h7]
    apply div_nonpos_of_nonpos_of_nonneg
    linarith 
    all_goals linarith 
    all_goals nlinarith
  linarith