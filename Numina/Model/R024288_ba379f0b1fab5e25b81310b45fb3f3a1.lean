import Mathlib

open Real

theorem inequalities_601984 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
  constructor
  · -- First part: 0 ≤ xy + yz + zx - 2xyz.
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    have hx1 : 0 ≤ x := by linarith
    have hy1 : 0 ≤ y := by linarith
    have hx2 : 0 ≤ 1 - x - y := by
      nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
      mul_nonneg hx1 hy1, 
      mul_nonneg hx1 (show 0 ≤ 1 - x - y by nlinarith), 
      mul_nonneg hy1 (show 0 ≤ 1 - x - y by nlinarith)
    ]
  · -- Second part: xy + yz + zx - 2xyz ≤ 7/27.
    have h1 : z = 1 - x - y := by linarith
    rw [h1]
    have hx1 : 0 ≤ x := by linarith
    have hy1 : 0 ≤ y := by linarith
    have hx2 : 0 ≤ 1 - x - y := by
      nlinarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
      mul_nonneg hx1 hy1, 
      mul_nonneg hx1 (show 0 ≤ 1 - x - y by nlinarith), 
      mul_nonneg hy1 (show 0 ≤ 1 - x - y by nlinarith), 
      sq_nonneg (x + y - (1 - x - y)), 
      sq_nonneg (x - 4 / 9), sq_nonneg (y - 4 / 9), sq_nonneg ((1 - x - y) - 1 / 9)
    ]