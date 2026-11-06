import Mathlib

theorem inequalities_4072 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hab : a * b = 1) (hcd : c * d = 1) :
    (a + b) * (c + d) + 4 ≥ 2 * (a + b + c + d) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), 
    sq_nonneg (a * c - 1), sq_nonneg (a * d - 1), sq_nonneg (b * c - 1), sq_nonneg (b * d - 1),
    mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
    mul_pos (show 0 < a * b by nlinarith) (show 0 < c * d by nlinarith)]