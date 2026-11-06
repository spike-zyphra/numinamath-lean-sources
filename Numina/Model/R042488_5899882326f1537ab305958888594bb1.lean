import Mathlib

theorem inequalities_54471 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a - b * c) / (a + b * c) + (b - c * a) / (b + c * a) + (c - a * b) / (c + a * b) ≤ 3 / 2 := by
  have h3 : a + b + c = 1 := h
  have h4 : c = 1 - a - b := by
    linarith
  rw [h4]
  have pos1 : 0 < a + b * (1 - a - b) := by
    nlinarith [show (0 : ℝ) < a by linarith, show (0 : ℝ) < (1 - a - b) by nlinarith, mul_pos ha (show (0 : ℝ) < (1 - a - b) by nlinarith)]
  have pos2 : 0 < b + (1 - a - b) * a := by
    nlinarith [show (0 : ℝ) < b by linarith, show (0 : ℝ) < (1 - a - b) by nlinarith, mul_pos hb (show (0 : ℝ) < (1 - a - b) by nlinarith)]
  have pos3 : 0 < (1 - a - b) + a * b := by
    nlinarith [show (0 : ℝ) < (1 - a - b) by nlinarith, show (0 : ℝ) < a by linarith, show (0 : ℝ) < b by linarith, mul_pos ha hb]
  have h6 : (a - b * (1 - a - b)) / (a + b * (1 - a - b)) + (b - (1 - a - b) * a) / (b + (1 - a - b) * a) + ((1 - a - b) - a * b) / ((1 - a - b) + a * b) - 3 / 2 ≤ 0 := by
    have pos1' : 0 < (a + b * (1 - a - b)) * (b + (1 - a - b) * a) * ((1 - a - b) + a * b) := by
      positivity
    have h7 : (a - b * (1 - a - b)) / (a + b * (1 - a - b)) + (b - (1 - a - b) * a) / (b + (1 - a - b) * a) + ((1 - a - b) - a * b) / ((1 - a - b) + a * b) - 3 / 2 = 
        ((a - b * (1 - a - b)) * (b + (1 - a - b) * a) * ((1 - a - b) + a * b) + (b - (1 - a - b) * a) * (a + b * (1 - a - b)) * ((1 - a - b) + a * b) + ((1 - a - b) - a * b) * (a + b * (1 - a - b)) * (b + (1 - a - b) * a) - 3 / 2 * ((a + b * (1 - a - b)) * (b + (1 - a - b) * a) * ((1 - a - b) + a * b))) / ((a + b * (1 - a - b)) * (b + (1 - a - b) * a) * ((1 - a - b) + a * b)) := by
      field_simp
      ring
    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is ≤ 0.
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)),
          sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), sq_nonneg ((1 - a - b) * a - a * b),
          mul_pos ha hb, mul_pos ha (show 0 < (1 - a - b : ℝ) by nlinarith), mul_pos hb (show 0 < (1 - a - b : ℝ) by nlinarith),
          mul_pos (show 0 < a * b by nlinarith) (show 0 < b * (1 - a - b) by nlinarith), 
          mul_pos (show 0 < b * (1 - a - b) by nlinarith) (show 0 < (1 - a - b) * a by nlinarith), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < (1 - a - b) * a by nlinarith), 
          mul_pos (show 0 < a by linarith) (show 0 < b * (1 - a - b) by nlinarith), 
          mul_pos (show 0 < b by linarith) (show 0 < a * (1 - a - b) by nlinarith), 
          mul_pos (show 0 < (1 - a - b) by nlinarith) (show 0 < a * b by nlinarith)
      ]
    · -- Show that the denominator is ≥ 0.
      positivity
  linarith [h6]