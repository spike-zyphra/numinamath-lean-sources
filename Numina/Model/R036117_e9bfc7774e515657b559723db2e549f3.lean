import Mathlib

theorem inequalities_600180 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + b) * (b + c) * (c + a) = 1) :
    a * b + b * c + c * a ≤ 3 / 4 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a + b + c - 3 / 2), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b from by nlinarith) (show 0 < b * c from by nlinarith), 
            mul_pos (show 0 < b * c from by nlinarith) (show 0 < c * a from by nlinarith), 
            mul_pos (show 0 < c * a from by nlinarith) (show 0 < a * b from by nlinarith)]