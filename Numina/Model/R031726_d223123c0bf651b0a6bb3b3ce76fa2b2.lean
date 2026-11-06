import Mathlib

theorem inequalities_62138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c ≤ a + b + c) :
    a^2 + b^2 + c^2 ≥ Real.sqrt 3 * a * b * c := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a * b * c - (a + b + c)), 
          sq_nonneg (a^2 + b^2 + c^2 - Real.sqrt 3 * a * b * c), 
          Real.sqrt_nonneg 3, 
          sq_nonneg (Real.sqrt 3 ^ 2 - 3), 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
          ]