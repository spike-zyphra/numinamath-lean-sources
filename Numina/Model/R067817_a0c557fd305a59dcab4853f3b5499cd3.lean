import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_132586 {x t : ℝ} (hx : x ≠ 3 / 2) (ht : t ^ 2 - 3 * t + 7 = 0)
  (h : x ^ 2 - 4 * x + 5 = t ^ 2 - 2 * t + 1) :
  dist (x, t) (3 / 2, -2 - 3 / 2) = 19 * sqrt 2 / 16 := by
  have h1 : t ^ 2 - 3 * t + 7 > 0 := by 
    nlinarith [sq_nonneg (t - 3 / 2)]
  nlinarith