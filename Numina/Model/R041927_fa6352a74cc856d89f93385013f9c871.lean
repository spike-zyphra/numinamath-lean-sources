import Mathlib

theorem inequalities_321707 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 1) :
    1 / (1 - a) + 1 / (1 - b) + 1 / (1 - c) ≥ 2 / (1 + a) + 2 / (1 + b) + 2 / (1 + c) := by
  have h1 : a < 1 := by nlinarith
  have h2 : b < 1 := by nlinarith
  have h3 : c < 1 := by nlinarith
  have ha1 : 0 < 1 - a := by nlinarith
  have hb1 : 0 < 1 - b := by nlinarith
  have hc1 : 0 < 1 - c := by nlinarith
  have ha2 : 0 < 1 + a := by linarith
  have hb2 : 0 < 1 + b := by linarith
  have hc2 : 0 < 1 + c := by linarith
  have h4 : 0 < (1 - a) * (1 - b) * (1 - c) := by positivity
  have h5 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
  have h6 : 0 < (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + b) * (1 + c) := by positivity
  have h7 : 1 / (1 - a) + 1 / (1 - b) + 1 / (1 - c) - (2 / (1 + a) + 2 / (1 + b) + 2 / (1 + c)) ≥ 0 := by 
    have h8 : 1 / (1 - a) + 1 / (1 - b) + 1 / (1 - c) - (2 / (1 + a) + 2 / (1 + b) + 2 / (1 + c)) =
        ((1 + a) * (1 + b) * (1 + c) * (1 - b) * (1 - c) + (1 + a) * (1 + b) * (1 + c) * (1 - a) * (1 - c) + (1 + a) * (1 + b) * (1 + c) * (1 - a) * (1 - b) - 2 * (1 - a) * (1 - b) * (1 - c) * (1 + b) * (1 + c) - 2 * (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + c) - 2 * (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + b)) / ((1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + b) * (1 + c)) := by
      field_simp
      ring
    rw [h8] at *
    apply div_nonneg
    -- Prove the numerator is non-negative.
    have h9 : ((1 + a) * (1 + b) * (1 + c) * (1 - b) * (1 - c) + (1 + a) * (1 + b) * (1 + c) * (1 - a) * (1 - c) + (1 + a) * (1 + b) * (1 + c) * (1 - a) * (1 - b) - 2 * (1 - a) * (1 - b) * (1 - c) * (1 + b) * (1 + c) - 2 * (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + c) - 2 * (1 - a) * (1 - b) * (1 - c) * (1 + a) * (1 + b)) ≥ 0 := by
      have h8 : c = 1 - a - b := by linarith 
      rw [h8]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (a * b - a * (1 - a - b)), sq_nonneg (a * (1 - a - b) - b * (1 - a - b)), 
          mul_pos ha hb, mul_pos hb (show (0 : ℝ) < 1 - a - b by nlinarith), 
          mul_pos ha (show (0 : ℝ) < 1 - a - b by nlinarith), 
          mul_pos (show (0 : ℝ) < 1 - a by nlinarith) (show (0 : ℝ) < 1 - b by nlinarith), 
          mul_pos (show (0 : ℝ) < 1 - a by nlinarith) (show (0 : ℝ) < 1 - a - b by nlinarith), 
          mul_pos (show (0 : ℝ) < 1 - b by nlinarith) (show (0 : ℝ) < 1 - a - b by nlinarith)
        ]
    linarith
    all_goals positivity
  linarith