import Mathlib

theorem inequalities_139497 (x y z : ℝ) (hx : 0 < z) (hy : z ≤ y) (hxy : y ≤ x) :
    x^2 * y / (y + z) + y^2 * z / (z + x) + z^2 * x / (x + y) ≥
    (1 / 2) * (x^2 + y^2 + z^2) := by
  have h1 : 0 < y + z := by linarith
  have h2 : 0 < z + x := by linarith
  have h3 : 0 < x + y := by linarith

  have h4 : x^2 * y / (y + z) + y^2 * z / (z + x) + z^2 * x / (x + y) - (1 / 2) * (x^2 + y^2 + z^2) ≥ 0 := by
    have h5 : x^2 * y / (y + z) + y^2 * z / (z + x) + z^2 * x / (x + y) - (1 / 2) * (x^2 + y^2 + z^2) =
        (x^2 * y * (z + x) * (x + y) + y^2 * z * (y + z) * (x + y) + z^2 * x * (y + z) * (z + x) - (1 / 2) * (x^2 + y^2 + z^2) * (y + z) * (z + x) * (x + y)) / ((y + z) * (z + x) * (x + y)) := by
      field_simp
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> field_simp
      <;> ring_nf
    rw [h5]

    apply div_nonneg
    · -- Prove numerator is non-negative
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (y - z)), sq_nonneg (x * (z - x)),
          sq_nonneg (y * (x - y)), sq_nonneg (y * (y - z)), sq_nonneg (y * (z - x)),
          sq_nonneg (z * (x - y)), sq_nonneg (z * (y - z)), sq_nonneg (z * (z - x)),
          mul_nonneg (show (0 : ℝ) ≤ x - y by linarith) (show (0 : ℝ) ≤ y - z by linarith),
          mul_nonneg (show (0 : ℝ) ≤ x - y by linarith) (show (0 : ℝ) ≤ z by linarith),
          mul_nonneg (show (0 : ℝ) ≤ y - z by linarith) (show (0 : ℝ) ≤ z by linarith)
          ]
    · -- Prove denominator is positive
      positivity
  linarith