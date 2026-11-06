import Mathlib

open Real Set

theorem algebra_11898 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c * (a + b + c) = 1) :
    2 ≤ (a + c) * (b + c) := by 
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a + b - c), sq_nonneg (a - b), sq_nonneg (c - (a * b / (a + b))), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
            mul_pos (show 0 < a * b from mul_pos ha hb) (show 0 < a + b + c from by nlinarith), 
            mul_pos (show 0 < a * c from mul_pos ha hc) (show 0 < b * c from mul_pos hb hc)]