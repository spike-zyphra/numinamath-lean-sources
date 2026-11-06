import Mathlib

theorem algebra_294031 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x + y / z = 2) (h2 : y + z / x = 2) (h3 : z + x / y = 2) :
    x + y + z = 3 := by
  have eq1 : x * z + y = 2 * z := by
    have hz' : z ≠ 0 := by linarith
    field_simp at h1
    linarith
  have eq2 : y * x + z = 2 * x := by
    have hx' : x ≠ 0 := by linarith
    field_simp at h2
    linarith
  have eq3 : z * y + x = 2 * y := by
    have hy' : y ≠ 0 := by linarith
    field_simp at h3
    linarith
  
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]