import Mathlib

theorem inequalities_46413 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) ≤ 1 / 2 := by 
  have ha1 : 2 * a + 1 > 0 := by 
    linarith
  have hb1 : 3 * b + 1 > 0 := by
    linarith
  have hc1 : 6 * c + 1 > 0 := by
    linarith
  have hx4 : a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) - 1 / 2 ≤ 0 := by
    have hx7 : a / (2 * a + 1) + b / (3 * b + 1) + c / (6 * c + 1) - 1 / 2 = 
          ( (a * (3 * b + 1) * (6 * c + 1) ) + (b * (2 * a + 1) * (6 * c + 1) ) + (c * (2 * a + 1) * (3 * b + 1) ) - (1 / 2) * (2 * a + 1) * (3 * b + 1) * (6 * c + 1) ) / ((2 * a + 1) * (3 * b + 1) * (6 * c + 1)) := by
      field_simp 
      ring
    rw [hx7] at *
    have hx8 : (a * (3 * b + 1) * (6 * c + 1) + b * (2 * a + 1) * (6 * c + 1) + c * (2 * a + 1) * (3 * b + 1) - (1 / 2) * (2 * a + 1) * (3 * b + 1) * (6 * c + 1) ) / ((2 * a + 1) * (3 * b + 1) * (6 * c + 1)) ≤ 0 := by 
      have hx9 : 0 < (2 * a + 1) * (3 * b + 1) * (6 * c + 1) := by positivity
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show numerator is ≤ 0
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 6), 
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc, 
          hsum, sq_nonneg (a * b - 1 / 36), sq_nonneg (a * c - 1 / 12), sq_nonneg (b * c - 1 / 18), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ c by linarith), 
          mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ c by linarith)
        ]
      · -- Show denominator is ≥ 0
        positivity 
    linarith
  linarith