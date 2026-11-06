import Mathlib

theorem inequalities_143997 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    10 * (a^3 + b^3 + c^3) - 9 * (a^5 + b^5 + c^5) ≥ 1 := by 
  have h1 : c = 1 - a - b := by linarith
  rw [h1] at *
  have h2 : 0 < (1 - a - b : ℝ) := by
    nlinarith 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
          sq_nonneg (a + b - (1 - a - b)), 
          mul_pos ha (show 0 < 1 - a - b by nlinarith ), 
          mul_pos hb (show 0 < 1 - a - b by nlinarith ), 
          mul_pos ha hb, 
          sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - (1 - a - b)^2), sq_nonneg (b^2 - (1 - a - b)^2)
           ]