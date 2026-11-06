import Mathlib

theorem inequalities_37834 (x y z : ℝ) :
    (x^2 - y^2) / (2 * x^2 + 1) + (y^2 - z^2) / (2 * y^2 + 1) +
    (z^2 - x^2) / (2 * z^2 + 1) ≤ 0 := by

  have hx1 : 2 * x^2 + 1 > 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy1 : 2 * y^2 + 1 > 0 := by
    nlinarith [sq_nonneg y, sq_nonneg x, sq_nonneg z]
  have hz1 : 2 * z^2 + 1 > 0 := by
    nlinarith [sq_nonneg z, sq_nonneg x, sq_nonneg y]

  have h5 : (2 * x^2 + 1) * (2 * y^2 + 1) * (2 * z^2 + 1) > 0 := by
    positivity

  have h6 : (x^2 - y^2) / (2 * x^2 + 1) + (y^2 - z^2) / (2 * y^2 + 1) + (z^2 - x^2) / (2 * z^2 + 1) - (0 : ℝ) ≤ 0 := by
    have h7 : (x^2 - y^2) / (2 * x^2 + 1) + (y^2 - z^2) / (2 * y^2 + 1) + (z^2 - x^2) / (2 * z^2 + 1) - (0 : ℝ) =
      ((x^2 - y^2) * (2 * y^2 + 1) * (2 * z^2 + 1) + (y^2 - z^2) * (2 * x^2 + 1) * (2 * z^2 + 1) + (z^2 - x^2) * (2 * x^2 + 1) * (2 * y^2 + 1)) / ((2 * x^2 + 1) * (2 * y^2 + 1) * (2 * z^2 + 1)) := by
      field_simp
      <;> ring
    rw [h7]
    apply div_nonpos_of_nonpos_of_nonneg

    · -- Prove numerator is non-positive.
      nlinarith [sq_nonneg (x^2 - 1 / 2), sq_nonneg (y^2 - 1 / 2), sq_nonneg (z^2 - 1 / 2),
        sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
        sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x)]

    · -- Prove denominator is non-negative.
      positivity

  linarith