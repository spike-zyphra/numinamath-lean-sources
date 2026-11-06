import Mathlib

theorem inequalities_598756 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    x / (2 * x ^ 2 + y ^ 2 + z ^ 2) +
    y / (x ^ 2 + 2 * y ^ 2 + z ^ 2) +
    z / (x ^ 2 + y ^ 2 + 2 * z ^ 2) ≤ 9 / 4 := by
  have h1 : 0 < y * z := by nlinarith
  have h2 : 0 < x * y := by nlinarith
  have h3 : 0 < x * z := by nlinarith

  have h4 : 2 * x ^ 2 + y ^ 2 + z ^ 2 > 0 := by nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h5 : x ^ 2 + 2 * y ^ 2 + z ^ 2 > 0 := by nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  have h6 : x ^ 2 + y ^ 2 + 2 * z ^ 2 > 0 := by nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]

  have h7 : x / (2 * x ^ 2 + y ^ 2 + z ^ 2) + y / (x ^ 2 + 2 * y ^ 2 + z ^ 2) + z / (x ^ 2 + y ^ 2 + 2 * z ^ 2) - 9 / 4 ≤ 0 := by
    have h8 : 0 < (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) * (x ^ 2 + y ^ 2 + 2 * z ^ 2) := by positivity
    have h9 : x / (2 * x ^ 2 + y ^ 2 + z ^ 2) + y / (x ^ 2 + 2 * y ^ 2 + z ^ 2) + z / (x ^ 2 + y ^ 2 + 2 * z ^ 2) - 9 / 4 =
        ( (x * (x^2 + 2*y^2 + z^2) * (x^2 + y^2 + 2*z^2) ) + (y * (2*x^2 + y^2 + z^2) * (x^2 + y^2 + 2*z^2) ) + (z * (2*x^2 + y^2 + z^2) * (x^2 + 2*y^2 + z^2) ) - (9/4) * (2*x^2 + y^2 + z^2) * (x^2 + 2*y^2 + z^2) * (x^2 + y^2 + 2*z^2) ) / ( (2 * x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 2 * y ^ 2 + z ^ 2) * (x ^ 2 + y ^ 2 + 2 * z ^ 2) ) := by
      field_simp
      ring
    rw [h9]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is ≤ 0
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)),
          sq_nonneg (y * (y - z)), sq_nonneg (y * (y - x)),
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          hsum, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]
    · -- Show that the denominator is ≥ 0
      positivity

  linarith