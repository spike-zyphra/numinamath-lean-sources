import Mathlib

theorem inequalities_599076 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 4 / (b ^ 2 + c ^ 2) + b ^ 4 / (c ^ 2 + a ^ 2) +
    c ^ 4 / (a ^ 2 + b ^ 2) ≥ (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
  have h1 : 0 < b ^ 2 + c ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h2 : 0 < c ^ 2 + a ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h3 : 0 < a ^ 2 + b ^ 2 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h4 : a ^ 4 / (b ^ 2 + c ^ 2) + b ^ 4 / (c ^ 2 + a ^ 2) + c ^ 4 / (a ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2 + c ^ 2) / 2 ≥ 0 := by
    have h5 : 0 < (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) * (a ^ 2 + b ^ 2) := by
      positivity
    have h6 : a ^ 4 / (b ^ 2 + c ^ 2) + b ^ 4 / (c ^ 2 + a ^ 2) + c ^ 4 / (a ^ 2 + b ^ 2) - (a ^ 2 + b ^ 2 + c ^ 2) / 2 = 
          (a ^ 4 * (c ^ 2 + a ^ 2) * (a ^ 2 + b ^ 2) + b ^ 4 * (b ^ 2 + c ^ 2) * (a ^ 2 + b ^ 2) + c ^ 4 * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) - (a ^ 2 + b ^ 2 + c ^ 2) / 2 * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) * (a ^ 2 + b ^ 2)) / ((b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) * (a ^ 2 + b ^ 2)) := by
      field_simp
      ring
    rw [h6]
    apply div_nonneg
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2), 
          sq_nonneg (a ^ 2 * (a ^ 2 - b ^ 2)), sq_nonneg (a ^ 2 * (a ^ 2 - c ^ 2)), sq_nonneg (a ^ 2 * (b ^ 2 - c ^ 2)), 
          sq_nonneg (b ^ 2 * (a ^ 2 - b ^ 2)), sq_nonneg (b ^ 2 * (a ^ 2 - c ^ 2)), sq_nonneg (b ^ 2 * (b ^ 2 - c ^ 2)), 
          sq_nonneg (c ^ 2 * (a ^ 2 - b ^ 2)), sq_nonneg (c ^ 2 * (a ^ 2 - c ^ 2)), sq_nonneg (c ^ 2 * (b ^ 2 - c ^ 2)), 
          sq_nonneg (a ^ 2 * b ^ 2 - b ^ 2 * c ^ 2), sq_nonneg (a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2), sq_nonneg (a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a ^ 2 by nlinarith) (show 0 < b ^ 2 by nlinarith), 
          mul_pos (show 0 < a ^ 2 by nlinarith) (show 0 < c ^ 2 by nlinarith), 
          mul_pos (show 0 < b ^ 2 by nlinarith) (show 0 < c ^ 2 by nlinarith)]
    all_goals
      positivity
  linarith