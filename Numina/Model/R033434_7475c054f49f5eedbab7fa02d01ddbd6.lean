import Mathlib

theorem algebra_260151 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 16) (h1 : a ≥ 3) : 2 * a + b + c ≥ 10 := by 
  nlinarith [sq_nonneg (a - 3), sq_nonneg (b - c), sq_nonneg (b + c - 4), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          h1]