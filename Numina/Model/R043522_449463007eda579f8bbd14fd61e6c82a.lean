import Mathlib

open Real

theorem inequalities_10123 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 2 * a + 4 * b + 7 * c ≤ 2 * a * b * c) :
    a + b + c ≥ 15 / 2 := by

  nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 5 / 2), sq_nonneg (c - 2), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a * b - 15 / 4), sq_nonneg (a * c - 21 / 4), sq_nonneg (b * c - 15 / 4)]