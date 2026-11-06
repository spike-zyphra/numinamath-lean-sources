import Mathlib

theorem inequalities_599178 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    16 * (a * b * c + b * c * d + c * d * a + d * a * b) ≤ (a + b + c + d) ^ 3 := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * d), sq_nonneg (c * d - d * a), sq_nonneg (d * a - a * b),
    sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
    sq_nonneg (a + b - c - d), sq_nonneg (a + d - b - c),
    mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]