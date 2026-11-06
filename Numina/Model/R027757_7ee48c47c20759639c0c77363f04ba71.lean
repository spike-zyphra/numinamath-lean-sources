import Mathlib

theorem inequalities_253966
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h : x * y + y * z + z * x ≤ 1) :
    (x + 1 / x) * (y + 1 / y) * (z + 1 / z) ≥ 8 * (x + y) * (y + z) * (z + x) := by

  have h1 : x + 1 / x = (x ^ 2 + 1) / x := by
    field_simp
    <;> nlinarith
  have h2 : y + 1 / y = (y ^ 2 + 1) / y := by
    field_simp
    <;> nlinarith
  have h3 : z + 1 / z = (z ^ 2 + 1) / z := by
    field_simp
    <;> nlinarith

  have h4 : (x + 1 / x) * (y + 1 / y) * (z + 1 / z) = (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) / (x * y * z) := by
    rw [h1, h2, h3]
    field_simp
    <;> nlinarith
  rw [h4]

  have h5 : x * y * z > 0 := by positivity

  suffices (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ≥ 8 * (x + y) * (y + z) * (z + x) * (x * y * z) by
    have h6 : (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) / (x * y * z) ≥ 8 * (x + y) * (y + z) * (z + x) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    linarith

  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x * y * z - 1), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
            mul_pos (show 0 < x * y from by nlinarith) (show 0 < y * z from by nlinarith),
            mul_pos (show 0 < y * z from by nlinarith) (show 0 < z * x from by nlinarith),
            mul_pos (show 0 < z * x from by nlinarith) (show 0 < x * y from by nlinarith),
            h]