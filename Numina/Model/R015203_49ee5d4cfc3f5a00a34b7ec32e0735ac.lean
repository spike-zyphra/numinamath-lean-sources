import Mathlib

theorem inequalities_105556 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) :
    a^2 / (b - 1) + b^2 / (a - 1) ≥ 8 := by 
  have h1 : 0 < b - 1 := by linarith 
  have h2 : 0 < a - 1 := by linarith 
  have h3 : 0 < (b - 1) * (a - 1) := mul_pos h1 h2 
  have h4 : a^2 / (b - 1) + b^2 / (a - 1) - 8 ≥ 0 := by 
    have h5 : (a^2 / (b - 1) + b^2 / (a - 1) - 8) = (a^2 * (a - 1) + b^2 * (b - 1) - 8 * ((b - 1) * (a - 1))) / ((b - 1) * (a - 1)) := by 
      field_simp 
      <;> ring
    rw [h5]
    have h6 : a^2 * (a - 1) + b^2 * (b - 1) - 8 * ((b - 1) * (a - 1)) ≥ 0 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), 
          sq_nonneg (a^2 - 4), sq_nonneg (b^2 - 4), 
          sq_nonneg (a - b), sq_nonneg (a^2 - b^2), 
          sq_nonneg (a * (a - 2) - b * (b - 2)), 
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), 
          mul_pos h1 h2
        ]
    apply div_nonneg 
    linarith 
    all_goals 
      positivity 
  linarith