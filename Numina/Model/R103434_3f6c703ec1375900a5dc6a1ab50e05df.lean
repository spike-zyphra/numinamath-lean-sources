import Mathlib

theorem algebra_13720 (a b c : ℝ) (ha : 3 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 16) :
    2 * a + b + c ≥ 10 := by 
  nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 2), sq_nonneg (c - 2),
    mul_pos hb hc, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]