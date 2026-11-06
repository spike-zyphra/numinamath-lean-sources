import Mathlib

theorem inequalities_599697
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (hxy : x ≥ y)
    (hyz : y ≥ z) :
    (x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y) ≥ x ^ 2 + y ^ 2 + z ^ 2 := by
  have h1 : 0 < x * y * z := by
    positivity
  have h2 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) ≥ 0 := by
    have pos1 : 0 < x * y * z := h1
    have h3 : x ^ 2 * y / z + y ^ 2 * z / x + z ^ 2 * x / y - (x ^ 2 + y ^ 2 + z ^ 2) =
        (x^3 * y^2 + y^3 * z^2 + x^2 * z^3 - (x^2 + y^2 + z^2) * (x * y * z)) / (x * y * z) := by
      field_simp
      <;> ring
      <;> field_simp <;> nlinarith
    rw [h3] at *
    apply div_nonneg
    -- Prove the numerator is non-negative
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
      mul_nonneg (show (0 : ℝ) ≤ x - y by nlinarith) (show (0 : ℝ) ≤ y - z by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ y - z by nlinarith) (show (0 : ℝ) ≤ z by linarith),
      mul_nonneg (show (0 : ℝ) ≤ x - y by nlinarith) (show (0 : ℝ) ≤ z by linarith),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
      mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y - z by nlinarith)
    ]
    all_goals
      positivity
  linarith