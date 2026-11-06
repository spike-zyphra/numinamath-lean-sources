import Mathlib

theorem inequalities_598610 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 2) :
    (1 - a) * (1 - b) / (a * b) + (1 - b) * (1 - c) / (b * c) +
    (1 - c) * (1 - a) / (c * a) ≥ 3 / 4 := by

  have h1 : 0 < a * b * c := by 
    positivity 
  have h3 : (1 - a) * (1 - b) / (a * b) + (1 - b) * (1 - c) / (b * c) + (1 - c) * (1 - a) / (c * a) - 3 / 4 ≥ 0 := by 
    have h4 : 0 < a * b * c := h1 
    have h5 : (1 - a) * (1 - b) / (a * b) + (1 - b) * (1 - c) / (b * c) + (1 - c) * (1 - a) / (c * a) - 3 / 4 = 
          ((1 - a) * (1 - b) * c + (1 - b) * (1 - c) * a + (1 - c) * (1 - a) * b - (3 / 4) * (a * b * c)) / (a * b * c) := by 
      field_simp
      ring 
    rw [h5] at *
    have pos1 : 0 < a * b * c := h1 
    apply div_nonneg 
    -- Show the numerator $\ge 0$.
    have h7 : 0 ≤ (1 - a) * (1 - b) * c + (1 - b) * (1 - c) * a + (1 - c) * (1 - a) * b - 3 / 4 * (a * b * c) := by 
      have h8 : c = 2 - a - b := by linarith 
      rw [h8] 
      have h9 : a + b < 2 := by nlinarith 
      have h10 : a * b > 0 := mul_pos ha hb 
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - (2 - a - b)), sq_nonneg (b - (2 - a - b)), 
                sq_nonneg (a + b - (2 - a - b)), 
                sq_nonneg (a * b - (1/9)), 
                sq_nonneg (a * (2 - a - b) - (1/9)), 
                sq_nonneg (b * (2 - a - b) - (1/9)), 
                mul_pos ha hb, 
                mul_pos ha (show (0 : ℝ) < 2 - a - b by nlinarith), 
                mul_pos hb (show (0 : ℝ) < 2 - a - b by nlinarith)
                ]
    exact h7 
    all_goals positivity 
  linarith