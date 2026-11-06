import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_174364 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^3 + y^3 - 5 * x * y ≥ -125 / 27 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - 5 / 3), sq_nonneg (y - 5 / 3), 
            mul_nonneg hx hy, 
            sq_nonneg (x - y), 
            sq_nonneg ((x - 5/3) - (y - 5/3)), 
            mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith)
            ]