import Mathlib

open Real

theorem inequalities_3000 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z + 2 = x * y * z) :
    2 * (y + z) * (z + x) * (x + y) / (x * y * z) + 6 * (1 / x + 1 / y + 1 / z) ≥ 25 := by 
  have hx1 : x * y * z > 0 := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz
  
  have h1 : 2 * (y + z) * (z + x) * (x + y) + 6 * (x * y + x * z + y * z) - 25 * (x * y * z) ≥ 0 := by 
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
              sq_nonneg (x * y + x * z + y * z - 4), sq_nonneg (x + y + z - 4),
              mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, 
              h, 
              mul_nonneg (show 0 ≤ x from by linarith) (show 0 ≤ y from by linarith), 
              mul_nonneg (show 0 ≤ x from by linarith) (show 0 ≤ z from by linarith), 
              mul_nonneg (show 0 ≤ y from by linarith) (show 0 ≤ z from by linarith)
            ]
  
  have h2 : 2 * (y + z) * (z + x) * (x + y) / (x * y * z) + 6 * (1 / x + 1 / y + 1 / z) - 25 ≥ 0 := by
    have pos1 : x * y * z > 0 := hx1
    have eq1 : 2 * (y + z) * (z + x) * (x + y) / (x * y * z) + 6 * (1 / x + 1 / y + 1 / z) - 25 =
        (2 * (y + z) * (z + x) * (x + y) + 6 * (x * y + x * z + y * z) - 25 * (x * y * z)) / (x * y * z) := by 
      field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
      ring
    rw [eq1]
    have hx1 : x * y * z > 0 := hx1
    have h3 : 2 * (y + z) * (z + x) * (x + y) + 6 * (x * y + x * z + y * z) - 25 * (x * y * z) ≥ 0 := h1
    have h4 : (2 * (y + z) * (z + x) * (x + y) + 6 * (x * y + x * z + y * z) - 25 * (x * y * z)) / (x * y * z) ≥ 0 := by
      apply div_nonneg
      linarith
      linarith
    linarith
  
  linarith