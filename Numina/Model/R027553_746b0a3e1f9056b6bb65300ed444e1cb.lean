import Mathlib

theorem inequalities_89779 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (a - b)^2 + (b - c)^2 + (c - a)^2 ≥ (1 - 27 * a * b * c) / 2 := by 
  have ha1 : c = 1 - a - b := by
    linarith
  rw [ha1]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a + b - (1 - a - b)), 
          mul_pos ha hb, mul_pos hb (show 0 < (1 - a - b : ℝ) by nlinarith), 
          mul_pos ha (show 0 < (1 - a - b : ℝ) by nlinarith), 
          sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ b * (1 - a - b) by nlinarith), 
          mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ a * (1 - a - b) by nlinarith), 
          mul_nonneg (show 0 ≤ b * (1 - a - b) by nlinarith) (show 0 ≤ a * (1 - a - b) by nlinarith)
]