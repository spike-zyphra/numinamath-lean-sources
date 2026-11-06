import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_321769 (x y : ℝ) (h : 2*x^2+3*y^2=1) :
    x+y ≤ 5*sqrt 6 / 6 ∧ x+y ≥ -5*sqrt 6 / 6 := by
  have h1 : x + y ≤ 5 * sqrt 6 / 6 := by
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num),
      sq_nonneg (x - 5 * sqrt 6 / 12), sq_nonneg (y - 5 * sqrt 6 / 12),
      Real.sqrt_pos.mpr (show 0 < (6 : ℝ) by norm_num),
      sq_nonneg (x - (-5 * sqrt 6 / 12)), sq_nonneg (y - (-5 * sqrt 6 / 12)),
      sq_nonneg (y + (2 / 3) * x), sq_nonneg (sqrt 6 ^ 2 - 6), Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num),
      Real.sqrt_pos.mpr (show 0 < (6 : ℝ) by norm_num) ]
  have h2 : x + y ≥ -5 * sqrt 6 / 6 := by
    nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num),
      sq_nonneg (x + 5 * sqrt 6 / 12), sq_nonneg (y + 5 * sqrt 6 / 12),
      Real.sqrt_pos.mpr (show 0 < (6 : ℝ) by norm_num),
      sq_nonneg (x - (-5 * sqrt 6 / 12)), sq_nonneg (y - (-5 * sqrt 6 / 12)),
      sq_nonneg (y + (2 / 3) * x), sq_nonneg (sqrt 6 ^ 2 - 6), Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num),
      Real.sqrt_pos.mpr (show 0 < (6 : ℝ) by norm_num) ]
  constructor
  · linarith
  · linarith