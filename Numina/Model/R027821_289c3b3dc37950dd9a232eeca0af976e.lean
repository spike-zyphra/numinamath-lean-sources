import Mathlib

theorem inequalities_303917 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a^2 + b^2 + c^2 + d^2 = 1) :
    (a + b)^4 + (a + c)^4 + (a + d)^4 + (b + c)^4 +
    (b + d)^4 + (c + d)^4 ≤ 6 := by 
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (a^2 - d^2), 
          sq_nonneg (b^2 - c^2), sq_nonneg (b^2 - d^2), sq_nonneg (c^2 - d^2),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
          sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, 
          mul_pos hc hd,
          sq_nonneg (a + b + c + d)
        ]