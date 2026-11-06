import Mathlib

theorem inequalities_600564 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    (x + y - 1) ^ 2 / z + (y + z - 1) ^ 2 / x + (z + x - 1) ^ 2 / y ≥ x + y + z := by
  have h1 : (x + y - 1) ^ 2 / z + (y + z - 1) ^ 2 / x + (z + x - 1) ^ 2 / y - (x + y + z) ≥ 0 := by
    have hx2 : 0 < x * y * z := by positivity
    have hx3 : (x + y - 1) ^ 2 / z + (y + z - 1) ^ 2 / x + (z + x - 1) ^ 2 / y - (x + y + z) =
      ( (x + y - 1) ^ 2 * (x * y) + (y + z - 1) ^ 2 * (y * z) + (z + x - 1) ^ 2 * (x * z) - (x + y + z) * (x * y * z) ) / (x * y * z) := by 
      field_simp 
      ring
    rw [hx3]
    have hx4 : ( (x + y - 1) ^ 2 * (x * y) + (y + z - 1) ^ 2 * (y * z) + (z + x - 1) ^ 2 * (x * z) - (x + y + z) * (x * y * z) ) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
      ]
    have hx5 : x * y * z > 0 := by positivity
    exact div_nonneg hx4 (by positivity)
  linarith