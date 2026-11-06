import Mathlib

theorem algebra_5327 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^3 + b^3 + c^3 = 8) :
    a * (b + c) ≤ 4 := by 
  nlinarith [sq_nonneg (a - 2), sq_nonneg (b - c), sq_nonneg (a^2 - 2), sq_nonneg (b + c - 2), 
          sq_nonneg (a^2 - (b + c)), 
          sq_nonneg (b - c), 
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]