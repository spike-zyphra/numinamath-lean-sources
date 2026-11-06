import Mathlib

theorem inequalities_47342 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * (2 * x - y) / (y * (2 * z + x)) + y * (2 * y - z) / (z * (2 * x + y)) +
    z * (2 * z - x) / (x * (2 * y + z)) ≥ 1 := by
  have h3 : x * (2 * x - y) / (y * (2 * z + x)) + y * (2 * y - z) / (z * (2 * x + y)) + z * (2 * z - x) / (x * (2 * y + z)) - 1 ≥ 0 := by
    have pos1 : 0 < x := by linarith
    have pos2 : 0 < y := by linarith
    have pos3 : 0 < z := by linarith
    have pos1'1 : 0 < y * (2 * z + x) := by positivity
    have pos1'2 : 0 < z * (2 * x + y) := by positivity
    have pos1'3 : 0 < x * (2 * y + z) := by positivity
    have h4 : x * (2 * x - y) / (y * (2 * z + x)) + y * (2 * y - z) / (z * (2 * x + y)) + z * (2 * z - x) / (x * (2 * y + z)) - 1 =
        (x * (2 * x - y) * z * (2 * x + y) * x * (2 * y + z) + y * (2 * y - z) * y * (2 * z + x) * x * (2 * y + z) + z * (2 * z - x) * y * (2 * z + x) * z * (2 * x + y) - y * (2 * z + x) * z * (2 * x + y) * x * (2 * y + z)
      ) / (y * (2 * z + x) * z * (2 * x + y) * x * (2 * y + z)
      ) := by 
      field_simp
      ring
    rw [h4] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
      sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
      sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
      sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
      mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
      mul_pos (show 0 < x * y by positivity) (show 0 < y * z by positivity), 
      mul_pos (show 0 < y * z by positivity) (show 0 < z * x by positivity), 
      mul_pos (show 0 < z * x by positivity) (show 0 < x * y by positivity)
      ]
    positivity
  linarith