import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_321800 (x y : ℝ) (h : (x-2)^2+(y-2)^2=1) :
    x*y ≤ (9+4*sqrt 2)/2 ∧ x*y ≥ (9-4*sqrt 2)/2 := by
  constructor
  · -- Prove the upper bound: x*y ≤ (9+4*sqrt 2)/2
    nlinarith [sq_nonneg (x - (2 + Real.sqrt 2 / 2)), sq_nonneg (y - (2 + Real.sqrt 2 / 2)), 
      sq_nonneg (x + y - (4 + Real.sqrt 2)), 
      Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      sq_nonneg (x - y)]
  · -- Prove the lower bound: x*y ≥ (9-4*sqrt 2)/2
    nlinarith [sq_nonneg (x - (2 - Real.sqrt 2 / 2)), sq_nonneg (y - (2 - Real.sqrt 2 / 2)), 
      sq_nonneg (x + y - (4 - Real.sqrt 2)), 
      Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
      sq_nonneg (x - y)]