import Mathlib

open Real

theorem inequalities_597334 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
  constructor
  · -- Prove the left inequality: 0 ≤ x * y + y * z + z * x - 2 * x * y * z
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ (1 - x - y : ℝ) by nlinarith), mul_nonneg hy (show 0 ≤ (1 - x - y : ℝ) by nlinarith)]
  · -- Prove the right inequality: x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), sq_nonneg (x + y - (1 - x - y)), sq_nonneg (x - 1/3), sq_nonneg (y - 1/3), sq_nonneg ((1 - x - y) - 1/3), mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ (1 - x - y : ℝ) by nlinarith), mul_nonneg hy (show 0 ≤ (1 - x - y : ℝ) by nlinarith)]