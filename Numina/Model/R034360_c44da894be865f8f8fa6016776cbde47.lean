import Mathlib

theorem algebra_599360 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b + c = 12) (h2 : a * b + b * c + c * a = 45) :
    a * b * c ≤ 54 := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a + b + c - 9), sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (c - 3),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
  ]