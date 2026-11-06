import Mathlib

theorem inequalities_27343 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) :
    2 * (a * b + b * c + c * a) ≤ 5 + a * b * c := by
  have ha1 : c = 3 - a - b := by linarith 
  rw [ha1]
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg ( (3 - a - b) - 1 ), 
          mul_pos ha hb, mul_pos hb (show (3 - a - b) > 0 by nlinarith), 
          mul_pos ha (show (3 - a - b) > 0 by nlinarith), 
          sq_nonneg (a - b), sq_nonneg (b - (3 - a - b)), sq_nonneg (a - (3 - a - b)), 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < (3 - a - b) by nlinarith)]