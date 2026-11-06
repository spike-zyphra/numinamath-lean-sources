import Mathlib

theorem inequalities_122316 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a < b + c) :
    a / (1 + a) < b / (1 + b) + c / (1 + c) := by
  have h1 : 0 < (1 + a) := by linarith
  have h2 : 0 < (1 + b) := by linarith
  have h3 : 0 < (1 + c) := by linarith
  have h4 : 0 < (1 + b) * (1 + c) := mul_pos h2 h3
  have h5 : a / (1 + a) - (b / (1 + b) + c / (1 + c)) < 0 := by
    have h6 : a * (1 + b) * (1 + c) < b * (1 + a) * (1 + c) + c * (1 + a) * (1 + b) := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (sub_pos.mpr h) (show 0 < (b * c) by positivity), 
          mul_pos (sub_pos.mpr h) (show 0 < b by linarith), 
          mul_pos (sub_pos.mpr h) (show 0 < c by linarith), 
          sq_nonneg (a - (b + c)), sq_nonneg (b - c)]
    have h7 : a / (1 + a) - (b / (1 + b) + c / (1 + c)) = (a * (1 + b) * (1 + c) - (b * (1 + a) * (1 + c) + c * (1 + a) * (1 + b))) / ((1 + a) * (1 + b) * (1 + c)) := by
      field_simp
      <;> ring
    rw [h7] at *
    apply div_neg_of_neg_of_pos
    · -- Show the numerator is negative
      linarith
    · -- Show the denominator is positive
      positivity
  linarith