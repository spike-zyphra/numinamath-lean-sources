import Mathlib

theorem algebra_311431 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + c) * (b ^ 2 + a * c) = 4 * a) :
    b + c ≤ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (b + c - 2), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]