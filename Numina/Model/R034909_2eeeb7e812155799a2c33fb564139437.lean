import Mathlib

theorem inequalities_30052 (x y z : ℝ) :
    (y^2 - x^2) / (2 * x^2 + 1) + (z^2 - y^2) / (2 * y^2 + 1) +
    (x^2 - z^2) / (2 * z^2 + 1) ≥ 0 := by
  have h1 : 2 * x^2 + 1 > 0 := by
    positivity
  have h2 : 2 * y^2 + 1 > 0 := by
    positivity
  have h3 : 2 * z^2 + 1 > 0 := by
    positivity
  have h4 : (y^2 - x^2) / (2 * x^2 + 1) + (z^2 - y^2) / (2 * y^2 + 1) + (x^2 - z^2) / (2 * z^2 + 1) =
      ((y ^ 2 - x ^ 2) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) + (z ^ 2 - y ^ 2) * (2 * x ^ 2 + 1) * (2 * z ^ 2 + 1) + (x ^ 2 - z ^ 2) * (2 * x ^ 2 + 1) * (2 * y ^ 2 + 1)) / ((2 * x ^ 2 + 1) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1)) := by
    field_simp
    ring
  rw [h4]
  have h5 : (2 * x^2 + 1) * (2 * y^2 + 1) * (2 * z^2 + 1) > 0 := by
    positivity
  have h6 : (y ^ 2 - x ^ 2) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) + (z ^ 2 - y ^ 2) * (2 * x ^ 2 + 1) * (2 * z ^ 2 + 1) + (x ^ 2 - z ^ 2) * (2 * x ^ 2 + 1) * (2 * y ^ 2 + 1) ≥ 0 := by
    nlinarith [sq_nonneg (x * y * z), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), mul_nonneg (sq_nonneg x) (sq_nonneg (y^2 - z^2)), mul_nonneg (sq_nonneg y) (sq_nonneg (z^2 - x^2)), mul_nonneg (sq_nonneg z) (sq_nonneg (x^2 - y^2)), sq_nonneg (x * y * z - x * z ^ 2), sq_nonneg (y * x * z - y * x ^ 2)]
  apply div_nonneg
  linarith
  positivity