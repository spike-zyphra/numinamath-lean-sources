import Mathlib

theorem inequalities_597329 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have h1 : 0 < b + c := by linarith 
  have h2 : 0 < c + a := by linarith 
  have h3 : 0 < a + b := by linarith 
  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have h5 : (a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ) =
      ( (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) ) / (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp [h1, h2, h3]
      ring
    rw [h5]
    have h6 : 2 * (b + c) * (c + a) * (a + b) > 0 := by positivity
    have h7 : (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) ≥ 0 := by 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
         ]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith