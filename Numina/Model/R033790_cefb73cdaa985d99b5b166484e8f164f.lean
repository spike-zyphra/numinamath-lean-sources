import Mathlib

theorem inequalities_300841 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * y / (x^2 + y^2 + 2 * z^2) +
    y * z / (2 * x^2 + y^2 + z^2) +
    z * x / (x^2 + 2 * y^2 + z^2) ≤ 3 / 4 := by

  have h1 : 0 < x^2 := by nlinarith
  have h2 : 0 < y^2 := by nlinarith
  have h3 : 0 < z^2 := by nlinarith

  have h4 : 0 < x^2 + y^2 + 2 * z^2 := by
    linarith [h1, h2, h3]
  have h5 : 0 < 2 * x^2 + y^2 + z^2 := by
    linarith [h1, h2, h3]
  have h6 : 0 < x^2 + 2 * y^2 + z^2 := by
    linarith [h1, h2, h3]

  have h7 : x * y / (x^2 + y^2 + 2 * z^2) +
    y * z / (2 * x^2 + y^2 + z^2) +
    z * x / (x^2 + 2 * y^2 + z^2) - 3 / 4 ≤ 0 := by
    have h8 : x * y / (x^2 + y^2 + 2 * z^2) + y * z / (2 * x^2 + y^2 + z^2) + z * x / (x^2 + 2 * y^2 + z^2) - 3 / 4 =
        (x * y * (2 * x^2 + y^2 + z^2) * (x^2 + 2 * y^2 + z^2) +
        y * z * (x^2 + y^2 + 2 * z^2) * (x^2 + 2 * y^2 + z^2) +
        z * x * (x^2 + y^2 + 2 * z^2) * (2 * x^2 + y^2 + z^2) - 3 / 4 * (x^2 + y^2 + 2 * z^2) * (2 * x^2 + y^2 + z^2) * (x^2 + 2 * y^2 + z^2)) / ((x^2 + y^2 + 2 * z^2) * (2 * x^2 + y^2 + z^2) * (x^2 + 2 * y^2 + z^2)) := by
      field_simp
      ring
    rw [h8] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show the numerator is ≤ 0
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3
        ]
    · -- Show the denominator is ≥ 0
      positivity

  linarith