import Mathlib

theorem inequalities_212105
    (x y z t : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hz : 0 ≤ z)
    (ht : 0 ≤ t)
    (hxyz : x * y * z = 2)
    (hsum : y + z + t = 2 * Real.sqrt 2) :
    6 ≤ 2 * x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 := by

  have ht_eq : t = 2 * Real.sqrt 2 - (y + z) := by linarith
  rw [ht_eq]

  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - Real.sqrt 2), sq_nonneg (z - Real.sqrt 2), sq_nonneg (y * z - 2), sq_nonneg (x * (y * z - 2)), sq_nonneg (y - z), sq_nonneg ((2 * Real.sqrt 2 - (y + z)) ), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (x - 1), mul_nonneg hx hy, mul_nonneg hx hz, mul_nonneg hy hz ]