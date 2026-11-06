import Mathlib

open Real

theorem inequalities_4979
  (a b c : ℝ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (h : a * b + b * c + c * a = 3) :
  (a ^ 2 + b) * (b ^ 2 + c) * (c ^ 2 + a) ≥ 8 := by
  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          sq_nonneg (a * b * c - 1),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]