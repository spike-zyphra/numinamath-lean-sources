import Mathlib

open Real

theorem inequalities_60190 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) : a * b + b * c + c * d ≤ 1 / 4 := by
  have h1 : a + b + c + d = 1 := h
  nlinarith [sq_nonneg (a + c - (b + d)), sq_nonneg (a - c), sq_nonneg (b - d), 
    sq_nonneg (a + c + b + d - 1), 
    mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
    mul_pos hb hc, mul_pos hb hd, 
    mul_pos hc hd]