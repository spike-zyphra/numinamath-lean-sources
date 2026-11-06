import Mathlib

theorem inequalities_101324 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 3) :
    (x^2 + y * z) / (x^2 + y * z + 1) + (y^2 + z * x) / (y^2 + z * x + 1) +
    (z^2 + x * y) / (z^2 + x * y + 1) ≤ 2 := by
  have h1 : x^2 + y^2 + z^2 = 3 := h
  have pos1 : 0 < x^2 + y * z + 1 := by positivity
  have pos2 : 0 < y^2 + z * x + 1 := by positivity
  have pos3 : 0 < z^2 + x * y + 1 := by positivity
  have h2 : (x^2 + y * z) / (x^2 + y * z + 1) + (y^2 + z * x) / (y^2 + z * x + 1) + (z^2 + x * y) / (z^2 + x * y + 1) - 2 ≤ 0 := by
    have pos1 : 0 < x^2 + y * z + 1 := by positivity
    have pos2 : 0 < y^2 + z * x + 1 := by positivity
    have pos3 : 0 < z^2 + x * y + 1 := by positivity
    have h3 : (x^2 + y * z) / (x^2 + y * z + 1) + (y^2 + z * x) / (y^2 + z * x + 1) + (z^2 + x * y) / (z^2 + x * y + 1) - 2 =
        ((x^2 + y * z) * (y^2 + z * x + 1) * (z^2 + x * y + 1) +
        (y^2 + z * x) * (x^2 + y * z + 1) * (z^2 + x * y + 1) +
        (z^2 + x * y) * (x^2 + y * z + 1) * (y^2 + z * x + 1) - 2 * (x^2 + y * z + 1) * (y^2 + z * x + 1) * (z^2 + x * y + 1)) / ((x^2 + y * z + 1) * (y^2 + z * x + 1) * (z^2 + x * y + 1)) := by
      field_simp
      ring
    rw [h3]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Prove the numerator is ≤ 0
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
        mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
      ]
    · -- Prove the denominator is ≥ 0
      positivity
  linarith