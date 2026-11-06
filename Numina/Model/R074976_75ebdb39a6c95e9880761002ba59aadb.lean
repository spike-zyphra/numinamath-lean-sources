import Mathlib

theorem inequalities_122200 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 := by
  have h1 : 0 < a * b * c := mul_pos (mul_pos ha hb) hc
  have h2 : a + b + c > 0 := by linarith [ha, hb, hc]
  have pos1 : b + c > 0 := by linarith
  have pos2 : a + c > 0 := by linarith
  have pos3 : a + b > 0 := by linarith
  
  have h3 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h4 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
      (a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - 3/2 * (b + c) * (a + c) * (a + b)) / ((b + c) * (a + c) * (a + b)) := by
      field_simp
      ring
    rw [h4]
    
    have h5 : a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - 3/2 * (b + c) * (a + c) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h6 : a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - 3/2 * (b + c) * (a + c) * (a + b) ≥ 0 := by linarith [h5]
    
    have h7 : (a * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - 3/2 * (b + c) * (a + c) * (a + b)) / ((b + c) * (a + c) * (a + b)) ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals
        positivity
    linarith

  linarith