import Mathlib

theorem inequalities_601153 (x y z : ℝ) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1)
    (hxyz : x * y * z = 1) :
    1 ≤ x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 := by
  have hx1 : x - 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have hy1 : y - 1 ≠ 0 := by
    intro h
    apply hy
    linarith
  have hz1 : z - 1 ≠ 0 := by
    intro h
    apply hz
    linarith
  have h1 : x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 - 1 ≥ 0 := by
    have eq1 : x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 - 1 =
        (x^2 * (y - 1)^2 * (z - 1)^2 + y^2 * (x - 1)^2 * (z - 1)^2 + z^2 * (x - 1)^2 * (y - 1)^2 - (x - 1)^2 * (y - 1)^2 * (z - 1)^2) / ((x - 1)^2 * (y - 1)^2 * (z - 1)^2) := by
      field_simp [(show (x - 1) ≠ 0 by assumption), (show (y - 1) ≠ 0 by assumption), (show (z - 1) ≠ 0 by assumption)]
      ring
    rw [eq1]
    have hx3 : (x - 1)^2 * (y - 1)^2 * (z - 1)^2 > 0 := by
      positivity
    have h2 : x^2 * (y - 1)^2 * (z - 1)^2 + y^2 * (x - 1)^2 * (z - 1)^2 + z^2 * (x - 1)^2 * (y - 1)^2 - (x - 1)^2 * (y - 1)^2 * (z - 1)^2 ≥ 0 := by
      nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), sq_nonneg (y * z - 1),
                sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
                sq_nonneg (x + y + z - 3), sq_nonneg (x * y + x * z + y * z - 3),
                sq_nonneg (x * y * z - 1), hxyz
                ]
    apply div_nonneg
    linarith [h2]
    positivity
  linarith