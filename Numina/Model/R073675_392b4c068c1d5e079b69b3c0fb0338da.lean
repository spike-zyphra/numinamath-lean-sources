import Mathlib

theorem algebra_157298 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    x + y^2 + z^3 ≤ 1 := by
  have h1 : z = 1 - x - y := by linarith [hsum]
  rw [h1]
  nlinarith [sq_nonneg (x - (1 - x - y)^2), sq_nonneg ((1 - x - y) - y), sq_nonneg ((1 - x - y) - y), sq_nonneg ((1 - x - y) - 1 / 2), sq_nonneg (y - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg ((1 - x - y) - x), sq_nonneg (x - (1 - x - y)), sq_nonneg ((1 - x - y) - 1), sq_nonneg (x + y - 1), mul_nonneg (show 0 ≤ (1 - x - y) by nlinarith) (show 0 ≤ y by nlinarith), mul_nonneg (show 0 ≤ (1 - x - y) by nlinarith) (show 0 ≤ x by nlinarith), mul_nonneg (show 0 ≤ y by nlinarith) (show 0 ≤ x by nlinarith)]