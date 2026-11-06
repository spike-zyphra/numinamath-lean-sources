import Mathlib

theorem inequalities_292935 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    2 * (x ^ 2 + y ^ 2 + z ^ 2) +
    4 / 3 * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) ≥ 5 := by
  have h1 : 0 < x ^ 2 + 1 := by nlinarith
  have h2 : 0 < y ^ 2 + 1 := by nlinarith
  have h3 : 0 < z ^ 2 + 1 := by nlinarith

  have h4 : 2 * (x ^ 2 + y ^ 2 + z ^ 2) + 4 / 3 * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) - 5 ≥ 0 := by
    have h5 : 0 < (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) := by positivity
    have h6 : 2 * (x ^ 2 + y ^ 2 + z ^ 2) + 4 / 3 * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) - 5 =
      (2 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) +
      4 / 3 * ((y ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (y ^ 2 + 1)) - 5 * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1)) /
      ((x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1)) := by
      field_simp
      <;> ring
    rw [h6]
    apply div_nonneg
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - 1 / 3), sq_nonneg (y * z - 1 / 3), sq_nonneg (z * x - 1 / 3),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, h]
    positivity
  linarith