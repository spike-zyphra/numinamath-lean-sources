import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_310261 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
  (hsum : x + y + z = 1) :
  (x - 1/6) * (y - 1/6) * (z - 1/6)^2 ≤ 25/1296 := by
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x + y - 2 / 3), sq_nonneg (x - y), sq_nonneg (x + y - 1 / 2),
            sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 6), sq_nonneg ((1 - x - y) - 1 / 6),
            mul_nonneg hx hy, mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith),
            mul_nonneg (show 0 ≤ 1 - x - y by nlinarith) hx
          ]