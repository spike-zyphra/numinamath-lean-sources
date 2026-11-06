import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_233806 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + 2 * b + 3 * c = a * b * c) :
  a * b * c ≥ 9 * sqrt 2 := by
  have h1 : 0 < a * b * c := by positivity
  have h4 : 6 * (a + 2 * b + 3 * c) = a * (2 * b) * (3 * c) := by
    nlinarith [h]
  nlinarith [sq_nonneg (a - 3 * Real.sqrt 2), sq_nonneg (b - 3 * Real.sqrt 2 / 2), sq_nonneg (c - Real.sqrt 2),
            Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            sq_nonneg (a * b - 9), sq_nonneg (a * c - 6), sq_nonneg (b * c - 3)
            ]