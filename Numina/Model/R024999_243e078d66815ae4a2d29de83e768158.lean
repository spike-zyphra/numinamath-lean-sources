import Mathlib

theorem inequalities_161604 (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) :
    3 ≤ (x + y + z + t) / 2 + 4 / (x * y + y * z + z * t + t * x) := by
  have h6 : (x + y + z + t) / 2 + 4 / (x * y + y * z + z * t + t * x) - 3 ≥ 0 := by
    have h1 : 0 < x * y + y * z + z * t + t * x := by positivity
    have h6' : (x + y + z + t) / 2 + 4 / (x * y + y * z + z * t + t * x) - 3 =
        ( ((x + y + z + t) * (x * y + y * z + z * t + t * x) ) + 8 - 6 * (x * y + y * z + z * t + t * x) ) / (2 * (x * y + y * z + z * t + t * x) ) := by
      field_simp
      ring
    rw [h6'] at *
    apply div_nonneg
    · -- Show that the numerator is nonnegative
      have h77 : ((x + y + z + t) * (x * y + y * z + z * t + t * x) ) + 8 - 6 * (x * y + y * z + z * t + t * x) ≥ 0 := by
        nlinarith [sq_nonneg (x + y + z + t - 4), sq_nonneg (x * y + y * z + z * t + t * x - 4), 
          sq_nonneg (x - z), sq_nonneg (y - t),
          sq_nonneg (x + z - (y + t)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hx ht, 
          mul_pos hy hz, mul_pos hy ht, 
          mul_pos hz ht, 
          sq_nonneg (x * y - z * t), sq_nonneg (y * z - x * t)
          ]
      linarith
    · -- Show that the denominator is positive
      positivity
  linarith [h6]