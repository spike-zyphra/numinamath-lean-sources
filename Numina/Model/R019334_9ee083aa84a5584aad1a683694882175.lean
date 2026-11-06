import Mathlib

open Real

theorem inequalities_167813 (a b : ℝ) (ha : 0 < b) (hb : b < a) :
    a^2 + 1 / (b * (a - b)) ≥ 4 := by 
  have h1 : 0 < a - b := by linarith 
  have h2 : 0 < b * (a - b) := mul_pos ha h1 
  have h3 : a^2 + 1 / (b * (a - b)) - 4 ≥ 0 := by 
    have h4 : a^2 + 1 / (b * (a - b)) - 4 = ( (a^2 - 4) * (b * (a - b)) + 1 ) / (b * (a - b)) := by 
      field_simp 
      ring 
    rw [h4] 
    apply div_nonneg
    · -- Show that the numerator is ≥ 0
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * (a - b) - 1), sq_nonneg (b * (a - b) - 1 / 2), sq_nonneg (a^2 - 2), sq_nonneg (a - 2 * b), sq_nonneg (a - Real.sqrt 2), sq_nonneg (b - Real.sqrt 2 / 2), 
          sq_pos_of_pos ha, sq_pos_of_pos h1, 
          mul_pos ha h1, 
          mul_pos ha (show (0 : ℝ) < a from by linarith), 
          mul_pos h1 (show (0 : ℝ) < a from by linarith)
      ]
    · -- Show that the denominator is ≥ 0 
      nlinarith 
  linarith