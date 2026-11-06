import Mathlib

theorem inequalities_196707 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    6 ≤ a + b + c + d + 8 / (a * b + b * c + c * d + d * a) := by
  have h1 : 0 < a * b + b * c + c * d + d * a := by
    positivity
  have h2 : a + b + c + d + 8 / (a * b + b * c + c * d + d * a) - 6 ≥ 0 := by
    have h3 : 0 < a * b + b * c + c * d + d * a := h1
    have h4 : a + b + c + d + 8 / (a * b + b * c + c * d + d * a) - 6 = 
      ( (a + b + c + d) * (a * b + b * c + c * d + d * a) - 6 * (a * b + b * c + c * d + d * a) + 8 ) / ( (a * b + b * c + c * d + d * a) ) := by
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    have h6 : (a + b + c + d) * (a * b + b * c + c * d + d * a) - 6 * (a * b + b * c + c * d + d * a) + 8 ≥ 0 := by
      nlinarith [sq_nonneg (a + b + c + d - 4), sq_nonneg (a * b + b * c + c * d + d * a - 4), sq_nonneg (a + c - (b + d)), sq_nonneg (a - b + c - d), sq_nonneg (a - b - c + d), sq_nonneg (a + b - c - d), sq_nonneg (a * b - c * d), sq_nonneg (b * c - d * a),
        mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, 
            mul_pos hc hd, 
              mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith)
        ]
    linarith [h6]
    all_goals
    positivity
  linarith [h2]