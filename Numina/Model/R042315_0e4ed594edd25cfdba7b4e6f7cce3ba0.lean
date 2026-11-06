import Mathlib

open Real

theorem inequalities_107149 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c ≥ a * b * c) :
    a^2 + b^2 + c^2 ≥ a * b * c * sqrt 3 := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a + b + c - a * b * c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          Real.sqrt_pos.mpr (show 0 < 3 by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
          sq_nonneg (a * b * c), sq_nonneg ((a + b + c) - a * b * c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
         ]