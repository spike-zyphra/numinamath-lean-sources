import Mathlib

theorem algebra_920 {x y z : ℝ} (h3 : x ≠ 0) (h1 : x / 3 = y) (h2 : y = z / 2) :
    (x * y + y * z + z * x) / (x ^ 2 - 3 * y ^ 2 + 4 * z ^ 2) = 1 / 2 := by
  have hx : x = 3 * y := by
    linarith
  have hz : z = 2 * y := by
    linarith
  have h4 : y ≠ 0 := by
    by_contra h
    have h5 : x = 0 := by
      rw [hx]
      rw [h] at *
      -- Since y = 0, x = 3 * 0 = 0
      linarith
    contradiction

  -- Show that numerator becomes 11 * y^2
  have h5 : x * y + y * z + z * x = 11 * y^2 := by
    rw [hx, hz]
    nlinarith

  -- Show that denominator becomes 22 * y^2
  have h6 : x ^ 2 - 3 * y ^ 2 + 4 * z ^ 2 = 22 * y^2 := by
    rw [hx, hz]
    nlinarith

  -- Substitute the computed numerator and denominator
  rw [h5, h6]

  -- Simplify the fraction
  have h7 : y^2 ≠ 0 := by
    exact pow_ne_zero 2 h4

  field_simp [h7]
  <;> nlinarith