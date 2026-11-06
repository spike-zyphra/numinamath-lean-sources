import Mathlib

open Real Set

theorem inequalities_6324 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a ^ 3 + b ^ 3 + c ^ 3 ≥ 3 := by
  nlinarith [sq_nonneg (a + b + c - 3),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]