import Mathlib

theorem inequalities_60804 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a + b = c + d) (h2 : a ^ 2 + b ^ 2 > c ^ 2 + d ^ 2) :
    a ^ 3 + b ^ 3 > c ^ 3 + d ^ 3 := by

  have h3 : a * b < c * d := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - c - d), sq_nonneg (a - c), sq_nonneg (b - d)]
  have h4 : a ^ 3 + b ^ 3 > c ^ 3 + d ^ 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), sq_nonneg (a + b - c - d), sq_nonneg (a - c), sq_nonneg (b - d), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]
  linarith