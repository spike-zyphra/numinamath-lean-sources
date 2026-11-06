import Mathlib

theorem algebra_290105 {x y z : ℝ} (h0 : x^3 + y^3 + z^3 = 1) (h1 : x^2 + y^2 + z^2 = 1) (h2 : x + y + z = 1) :
    x * y * z = 0 := by
  have h3 : x * y + x * z + y * z = 0 := by
    have h3 : (x + y + z) ^ 2 = x^2 + y^2 + z^2 + 2 * (x * y + x * z + y * z) := by
      ring
    rw [h2, h1] at h3
    linarith
  have h4 : x * y * z = 0 := by
    have h5 : (x + y + z) ^ 3 = x^3 + y^3 + z^3 + 3 * (x * y + x * z + y * z) * (x + y + z) - 3 * (x * y * z) := by
      ring_nf
    rw [h2, h3, h0] at h5 
    linarith
  exact h4