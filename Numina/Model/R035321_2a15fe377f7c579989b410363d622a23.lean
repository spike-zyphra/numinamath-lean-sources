import Mathlib
theorem algebra_607470 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxyz : x * y * z = 8) :
(x - 2) / (x + 1) + (y - 2) / (y + 1) + (z - 2) / (z + 1) ≤ 0:= by
  have h1 : (x - 2) / (x + 1) + (y - 2) / (y + 1) + (z - 2) / (z + 1) = 3 - 3 * (1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1)) := by
    field_simp
    <;> ring
  rw [h1] at *
  have h3 : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) ≥ 1 := by
    have hx1 : 0 < x + 1 := by linarith
    have hy1 : 0 < y + 1 := by linarith
    have hz1 : 0 < z + 1 := by linarith
    have hx2 : 0 < (x + 1) * (y + 1) * (z + 1) := by positivity
    have h4 : (1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) - 1) ≥ 0 := by
      have h5 : (1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) - 1) = ( (y + 1) * (z + 1) + (x + 1) * (z + 1) + (x + 1) * (y + 1) - (x + 1) * (y + 1) * (z + 1) ) / ((x + 1) * (y + 1) * (z + 1)) := by 
        field_simp
        <;> ring
      rw [h5] at *
      apply div_nonneg
      · -- Show the numerator is non-negative
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), 
          hxyz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
      all_goals positivity
    linarith
  linarith [h3]