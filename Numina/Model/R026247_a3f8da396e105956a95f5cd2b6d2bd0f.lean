import Mathlib

theorem inequalities_211990 (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (hxyz : x * y * z = 1) (hyzt : y + z + t = 2) :
    x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 ≥ 3 := by 
  have ht_eq : t = 2 - y - z := by linarith
  rw [ht_eq]
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          sq_nonneg (2 - y - z - 0), 
          mul_nonneg hx hy, mul_nonneg hy hz, 
          mul_nonneg hx hz, 
          hxyz, 
          sq_nonneg (y * z - 1), 
          sq_nonneg (x * y - 1), 
          sq_nonneg (x * z - 1)]