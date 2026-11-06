import Mathlib
theorem algebra_607161 (x y z : ℝ) : (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) +
(z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) ≤ 0 := by

  have hx1 : 0 < 2 * x ^ 2 + 1 := by
    nlinarith [sq_nonneg x]

  have hy1 : 0 < 2 * y ^ 2 + 1 := by
    nlinarith [sq_nonneg y]

  have hz1 : 0 < 2 * z ^ 2 + 1 := by
    nlinarith [sq_nonneg z]

  have h1 : (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) ≤ 0 := by

    have hx2 : 0 < (2 * x^2 + 1) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) := by
      positivity

    have hx3 : (x ^ 2 - y ^ 2) / (2 * x^2 + 1) + (y^2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x^2) / (2 * z ^ 2 + 1) ≤ 0 := by
      have hx4 : (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y^2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x^2) / (2 * z ^ 2 + 1) =
          ((x ^ 2 - y ^ 2) * (2 * y^2 + 1) * (2 * z ^ 2 + 1) + (y^2 - z ^ 2) * (2 * x^2 + 1) * (2 * z ^ 2 + 1) + (z ^ 2 - x^2) * (2 * x^2 + 1) * (2 * y^2 + 1)) / ((2 * x ^ 2 + 1) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1)) := by
        field_simp
        <;> ring
      rw [hx4] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Numerator ≤ 0
        nlinarith [sq_nonneg (x^2 - 1/2), sq_nonneg (y^2 - 1/2), sq_nonneg (z^2 - 1/2),
                  sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
                  sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x)]
      · -- Denominator ≥ 0
        positivity

    linarith
  linarith