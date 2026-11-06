import Mathlib

theorem inequalities_603103 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by
  have h1 : 0 < (1 + y) * (1 + z) * (1 + x) := by
    positivity
  have h2 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have h1' : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 =
        (x^3 * (1 + x) + y^3 * (1 + y) + z^3 * (1 + z) - 3/4 * ((1 + x) * (1 + y) * (1 + z)) ) / ((1 + y) * (1 + z) * (1 + x)) := by
      field_simp
      ring
    rw [h1']
    have h5 : x^3 * (1 + x) + y^3 * (1 + y) + z^3 * (1 + z) - 3 / 4 * ((1 + x) * (1 + y) * (1 + z)) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          hxyz, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz, mul_pos (mul_pos hx hy) hz]
    apply div_nonneg
    linarith [h5]
    positivity
  linarith