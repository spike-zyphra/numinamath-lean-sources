import Mathlib

theorem inequalities_603220 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * (z + x) / ((y + z) * (3 * x + y + 2 * z)) +
    y * (x + y) / ((z + x) * (2 * x + 3 * y + z)) +
    z * (y + z) / ((x + y) * (x + 2 * y + 3 * z)) ≥ 1 / 2 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  have h2 : 0 < (y + z) * (3 * x + y + 2 * z) * (z + x) * (2 * x + 3 * y + z) * (x + y) * (x + 2 * y + 3 * z) := by
    positivity 
  have h3 : x * (z + x) / ((y + z) * (3 * x + y + 2 * z)) + y * (x + y) / ((z + x) * (2 * x + 3 * y + z)) + z * (y + z) / ((x + y) * (x + 2 * y + 3 * z)) - 1 / 2 ≥ 0 := by
    have h4 : 0 < (y + z) * (3 * x + y + 2 * z) * (z + x) * (2 * x + 3 * y + z) * (x + y) * (x + 2 * y + 3 * z) := by
      positivity
    have h5 : x * (z + x) / ((y + z) * (3 * x + y + 2 * z)) + y * (x + y) / ((z + x) * (2 * x + 3 * y + z)) + z * (y + z) / ((x + y) * (x + 2 * y + 3 * z)) - 1 / 2 =
          (x * (z + x) * (z + x) * (2 * x + 3 * y + z) * (x + y) * (x + 2 * y + 3 * z) + 
           y * (x + y) * (y + z) * (3 * x + y + 2 * z) * (x + y) * (x + 2 * y + 3 * z) + 
           z * (y + z) * (y + z) * (3 * x + y + 2 * z) * (z + x) * (2 * x + 3 * y + z) - 
           1 / 2 * (y + z) * (3 * x + y + 2 * z) * (z + x) * (2 * x + 3 * y + z) * (x + y) * (x + 2 * y + 3 * z)
           ) / ((y + z) * (3 * x + y + 2 * z) * (z + x) * (2 * x + 3 * y + z) * (x + y) * (x + 2 * y + 3 * z)) := by 
        field_simp
        ring
    rw [h5] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - z)), 
              sq_nonneg (y * (y - x)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
              mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
              mul_pos hx (show 0 < x * y from by nlinarith), 
              mul_pos hx (show 0 < x * z from by nlinarith), 
              mul_pos hy (show 0 < y * z from by nlinarith)
            ]
    all_goals positivity
  linarith