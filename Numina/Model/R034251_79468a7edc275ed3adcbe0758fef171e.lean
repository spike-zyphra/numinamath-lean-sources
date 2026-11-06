import Mathlib

theorem inequalities_210147 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    36 ≤ 1 / x + 4 / y + 9 / z := by 
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 1 / x + 4 / y + 9 / z - 36 ≥ 0 := by
    have pos1 : 0 < x * y * z := h1
    have h3 : (1 / x + 4 / y + 9 / z - 36) = (y * z + 4 * x * z + 9 * x * y - 36 * (x * y * z)) / (x * y * z) := by
      field_simp
      ring
    rw [h3]
    apply div_nonneg
    · -- Show that the numerator is non-negative
      have h5 : y * z + 4 * x * z + 9 * x * y - 36 * (x * y * z) ≥ 0 := by 
        have h6 : x + y + z = 1 := h
        have hx1 : 0 < x := hx
        have hy1 : 0 < y := hy
        have hz1 : 0 < z := hz
        nlinarith [sq_nonneg (x - 1 / 6), sq_nonneg (y - 1 / 3), sq_nonneg (z - 1 / 2), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          h
        ]
      linarith 
    · -- Show that the denominator is positive 
      positivity
  linarith