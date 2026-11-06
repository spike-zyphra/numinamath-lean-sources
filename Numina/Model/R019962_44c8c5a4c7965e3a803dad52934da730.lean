import Mathlib

theorem inequalities_602569
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + a * b * c = 4) :
    a + b + c ≤ 3 := by 
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)]