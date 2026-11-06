import Mathlib

theorem inequalities_231127 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    (x - 1) / (y + 1) + (y - 1) / (z + 1) + (z - 1) / (x + 1) ≥ 0 := by
  have h1 : 0 < y + 1 := by linarith
  have h2 : 0 < z + 1 := by linarith
  have h3 : 0 < x + 1 := by linarith
  have h4 : (x - 1) / (y + 1) + (y - 1) / (z + 1) + (z - 1) / (x + 1) =
      ((x - 1) * (z + 1) * (x + 1) + (y - 1) * (y + 1) * (x + 1) + (z - 1) * (y + 1) * (z + 1)) / ((y + 1) * (z + 1) * (x + 1)) := by
    field_simp
    <;> ring
  rw [h4] at *
  have h5 : (y + 1) * (z + 1) * (x + 1) > 0 := by
    positivity
  have h7 : (x - 1) * (z + 1) * (x + 1) + (y - 1) * (y + 1) * (x + 1) + (z - 1) * (y + 1) * (z + 1) ≥ 0 := by
    have h8 : x * y * z = 1 := hxyz
    -- Prove that the numerator is non-negative
    have h9 : (x - 1) * (z + 1) * (x + 1) + (y - 1) * (y + 1) * (x + 1) + (z - 1) * (y + 1) * (z + 1) ≥ 0 := by
      nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          sq_nonneg (x * y * z - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          hxyz
      ]
    linarith
  apply div_nonneg 
  · linarith [h7]
  all_goals positivity