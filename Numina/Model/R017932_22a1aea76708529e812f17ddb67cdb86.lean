import Mathlib

theorem inequalities_308402 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 14) :
    14 ≤ a^5 + b^5 / 8 + c^5 / 27 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3), 
          sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 4), sq_nonneg (c^2 - 9), 
          sq_nonneg (a^3 - 1), sq_nonneg (b^3 - 8), sq_nonneg (c^3 - 27), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
]