import Mathlib

theorem inequalities_278095 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by

  have h1 : z = 1 - x - y := by linarith
  constructor
  · -- Prove 0 ≤ x * y + y * z + z * x - 2 * x * y * z
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
      mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ 1 - x - y by nlinarith), 
      mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith)]
  
  · -- Prove x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27
    rw [h1]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
      mul_nonneg hx hy, mul_nonneg hx (show 0 ≤ 1 - x - y by nlinarith), 
      mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith),
      sq_nonneg (x + y - (1 - x - y)), 
      sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 3), 
      sq_nonneg ((1 - x - y) - 1 / 3)]