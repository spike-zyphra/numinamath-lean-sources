import Mathlib

theorem inequalities_31397 (x y z : ℤ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x - y : ℝ) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) +
    (z - x) / (x * z + 2 * x + 1) ≥ 0 := by
  have hx1 : (x : ℝ) > 0 := by exact_mod_cast hx
  have hy1 : (y : ℝ) > 0 := by exact_mod_cast hy
  have hz1 : (z : ℝ) > 0 := by exact_mod_cast hz
  have h1 : (x * y + 2 * y + 1 : ℝ) > 0 := by
    have hx1' : (x : ℝ) > 0 := by exact_mod_cast hx
    have hy1' : (y : ℝ) > 0 := by exact_mod_cast hy
    nlinarith
  have h2 : (y * z + 2 * z + 1 : ℝ) > 0 := by
    have hy1' : (y : ℝ) > 0 := by exact_mod_cast hy
    have hz1' : (z : ℝ) > 0 := by exact_mod_cast hz
    nlinarith
  have h3 : (x * z + 2 * x + 1 : ℝ) > 0 := by
    have hx1' : (x : ℝ) > 0 := by exact_mod_cast hx
    have hz1' : (z : ℝ) > 0 := by exact_mod_cast hz
    nlinarith
  have h4 : (x - y : ℝ) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (x * z + 2 * x + 1) ≥ 0 := by
    have h5 : (x * y + 2 * y + 1 : ℝ) > 0 := h1
    have h6 : (y * z + 2 * z + 1 : ℝ) > 0 := h2
    have h7 : (x * z + 2 * x + 1 : ℝ) > 0 := h3
    have h8 : (x - y : ℝ) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (x * z + 2 * x + 1) =
              ((x - y : ℝ) * ((y * z + 2 * z + 1) * (x * z + 2 * x + 1)) + (y - z : ℝ) * ((x * y + 2 * y + 1) * (x * z + 2 * x + 1)) + (z - x : ℝ) * ((x * y + 2 * y + 1) * (y * z + 2 * z + 1))) / ((x * y + 2 * y + 1) * (y * z + 2 * z + 1) * (x * z + 2 * x + 1)) := by 
      field_simp
      ring
    rw [h8] at *
    apply div_nonneg
    · -- Show that the numerator is non-negative
      have h5 : ((x - y : ℝ) * ((y * z + 2 * z + 1) * (x * z + 2 * x + 1)) + (y - z : ℝ) * ((x * y + 2 * y + 1) * (x * z + 2 * x + 1)) + (z - x : ℝ) * ((x * y + 2 * y + 1) * (y * z + 2 * z + 1))) ≥ 0 := by
        nlinarith [sq_nonneg ((x : ℝ) * (y : ℝ) - (y : ℝ) * (z : ℝ)), sq_nonneg ((y : ℝ) * (z : ℝ) - (z : ℝ) * (x : ℝ)), sq_nonneg ((z : ℝ) * (x : ℝ) - (x : ℝ) * (y : ℝ)), 
                  sq_nonneg ((x - y : ℝ)), sq_nonneg ((y - z : ℝ)), sq_nonneg ((z - x : ℝ)), 
                  sq_nonneg ((x * y - y * z) : ℝ), sq_nonneg ((y * z - z * x) : ℝ), sq_nonneg ((z * x - x * y) : ℝ), 
                  mul_pos hx1 hy1, mul_pos hy1 hz1, mul_pos hx1 hz1, 
                  mul_pos hx1 (show (y * z : ℝ) > 0 by positivity), 
                  mul_pos hy1 (show (z * x : ℝ) > 0 by positivity), 
                  mul_pos hz1 (show (x * y : ℝ) > 0 by positivity)
                ]
      linarith
    · -- Show that the denominator is non-negative
      positivity
  linarith