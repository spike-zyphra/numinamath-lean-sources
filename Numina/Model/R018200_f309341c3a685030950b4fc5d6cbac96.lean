import Mathlib

theorem inequalities_38808 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    6 ≤ a^2 + b^2 + c^2 + a^2 * b + b^2 * c + c^2 * a := by
  have h1 : c = 3 - a - b := by
    linarith 
  rw [h1] 
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ((3 - a - b) - 1), 
            sq_nonneg (a * b - 1), sq_nonneg (b * (3 - a - b) - 1), sq_nonneg ((3 - a - b) * a - 1), 
            mul_pos ha hb, mul_pos hb (show 0 < 3 - a - b by nlinarith [show 0 < a by linarith, show 0 < b by linarith, h]), 
            mul_pos ha (show 0 < 3 - a - b by nlinarith [show 0 < a by linarith, show 0 < b by linarith, h])
          ]