import Mathlib

theorem inequalities_84995 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 2 < b * c) : b ^ 3 + a * c ^ 2 > a * b * (a + c) := by
  nlinarith [sq_pos_of_pos ha, sq_nonneg (b - a), sq_nonneg (c - a), sq_nonneg (b - c), sq_nonneg (c - b),
    sq_nonneg (b), sq_nonneg (c), sq_nonneg (a), 
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
    h
  ]