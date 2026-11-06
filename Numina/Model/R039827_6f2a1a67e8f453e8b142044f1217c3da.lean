import Mathlib

theorem inequalities_90318 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a / b + b / c + c / a) ^ 2 ≥ 3 / 2 * ((a + b) / c + (b + c) / a + (c + a) / b) := by
  have h5 : (a / b + b / c + c / a) ^ 2 - 3 / 2 * ((a + b) / c + (b + c) / a + (c + a) / b) ≥ 0 := by 
    have h1 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    have h7 : (a / b + b / c + c / a) ^ 2 - 3 / 2 * ((a + b) / c + (b + c) / a + (c + a) / b) =
        ((a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) ^ 2 - 3 / 2 * ((a + b) * a * b + (b + c) * b * c + (c + a) * c * a) * (a * b * c)) / ((a * b * c) ^ 2) := by 
      field_simp
      <;> ring_nf  
    rw [h7]
    apply div_nonneg
    nlinarith [sq_nonneg (a^2 * c - b^2 * a), sq_nonneg (b^2 * a - c^2 * b), sq_nonneg (c^2 * b - a^2 * c), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * c by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < a * c by nlinarith), 
          mul_pos (show 0 < b * c by nlinarith) (show 0 < a * c by nlinarith)]
    positivity
  linarith