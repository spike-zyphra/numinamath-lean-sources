import Mathlib

open Real Set

theorem algebra_301027 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    2 * x * y + y * z + 2 * z * x ≤ 4 / 7 := by
  have hz' : z = 1 - x - y := by
    linarith
  rw [hz']
  nlinarith [sq_nonneg (x - 3 / 7), sq_nonneg (y - 2 / 7), sq_nonneg ((1 - x - y) - 2 / 7), 
    mul_nonneg hx hy, mul_nonneg hx (show (0 : ℝ) ≤ 1 - x - y by nlinarith), 
    mul_nonneg hy (show (0 : ℝ) ≤ 1 - x - y by nlinarith), 
    sq_nonneg (x + y - (1 - x - y)), 
    sq_nonneg (x - (1 - x - y)), 
    sq_nonneg (y - (1 - x - y))]