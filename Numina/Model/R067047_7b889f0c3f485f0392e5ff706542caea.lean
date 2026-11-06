import Mathlib

theorem inequalities_59105 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b < c + d) : a * c + b * d > a * b := by
  nlinarith [sq_nonneg (a - c), sq_nonneg (b - d), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hd, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]