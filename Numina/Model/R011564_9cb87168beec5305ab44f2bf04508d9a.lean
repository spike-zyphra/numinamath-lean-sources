import Mathlib

theorem Inequalities_147869 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hd : d > 0) :
  a / (b + c + d) + b / (a + c + d) + c / (a + b + d) + d / (a + b + c) ≥ 4 / 3 
  := by
  have h₁ : 0 < b + c + d := by positivity
  have h₂ : 0 < a + c + d := by positivity
  have h₃ : 0 < a + b + d := by positivity
  have h₄ : 0 < a + b + c := by positivity
  have h5 : a / (b + c + d) + b / (a + c + d) + c / (a + b + d) + d / (a + b + c) - 4 / 3 ≥ 0 := by
    have h6 : a / (b + c + d) + b / (a + c + d) + c / (a + b + d) + d / (a + b + c) - 4 / 3 =
      (a * (a + c + d) * (a + b + d) * (a + b + c) + b * (b + c + d) * (a + b + d) * (a + b + c) + c * (b + c + d) * (a + c + d) * (a + b + c) + d * (b + c + d) * (a + c + d) * (a + b + d) - 4 / 3 * (b + c + d) * (a + c + d) * (a + b + d) * (a + b + c)) / ((b + c + d) * (a + c + d) * (a + b + d) * (a + b + c)) := by
      field_simp
      ring
    rw [h6] at *
    apply div_nonneg
    · -- Show the numerator is non-negative
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a + b - c - d), sq_nonneg (a + c - b - d), sq_nonneg (a + d - b - c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, 
          mul_pos hc hd 
        ]
    · -- Show the denominator is positive
      positivity
  linarith