import Mathlib

theorem inequalities_8470
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    (x - y) / (2 * y + x * y + 1) + (y - z) / (2 * z + y * z + 1) +
    (z - x) / (2 * x + x * z + 1) ≥ 0 := by

  have hx1 : 0 < 2 * y + x * y + 1 := by
    positivity
  have hy1 : 0 < 2 * z + y * z + 1 := by
    positivity
  have hz1 : 0 < 2 * x + x * z + 1 := by
    positivity

  have h6 : 0 < (2 * y + x * y + 1) * (2 * z + y * z + 1) * (2 * x + x * z + 1) := by positivity
  have h7 : (x - y) / (2 * y + x * y + 1) + (y - z) / (2 * z + y * z + 1) + (z - x) / (2 * x + x * z + 1) =
    ( (x - y) * (2 * z + y * z + 1) * (2 * x + x * z + 1) +
      (y - z) * (2 * y + x * y + 1) * (2 * x + x * z + 1) +
      (z - x) * (2 * y + x * y + 1) * (2 * z + y * z + 1) ) / ( (2 * y + x * y + 1) * (2 * z + y * z + 1) * (2 * x + x * z + 1) ) := by 
    field_simp
    ring

  rw [h7]

  apply div_nonneg
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          mul_pos (show 0 < x * y by positivity) (show 0 < y * z by positivity), 
          mul_pos (show 0 < x * y by positivity) (show 0 < z * x by positivity), 
          mul_pos (show 0 < y * z by positivity) (show 0 < z * x by positivity)
        ]
  all_goals positivity