import Mathlib

open Real

theorem inequalities_48889 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    1 / ((x + 1)^2 + y^2 + 1) +
    1 / ((y + 1)^2 + z^2 + 1) +
    1 / ((z + 1)^2 + x^2 + 1) ≤ 1 / 2 := by

  have h1 : 1 / ((x + 1)^2 + y^2 + 1) ≤ 1 / (2 * (x * y + x + 1)) := by
    have h2 : (x + 1) ^ 2 + y ^ 2 + 1 ≥ 2 * (x * y + x + 1) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - x)]
    have h3 : 2 * (x * y + x + 1) > 0 := by
      positivity
    have h4 : (x + 1)^2 + y^2 + 1 ≥ 2 * (x * y + x + 1) := h2
    have h5 : (x + 1)^2 + y^2 + 1 > 0 := by positivity
    apply one_div_le_one_div_of_le
    all_goals
      try linarith
  have h2 : 1 / ((y + 1)^2 + z^2 + 1) ≤ 1 / (2 * (y * z + y + 1)) := by
    have h2 : (y + 1) ^ 2 + z ^ 2 + 1 ≥ 2 * (y * z + y + 1) := by
      nlinarith [sq_nonneg (y - z), sq_nonneg (z - y)]
    have h3 : 2 * (y * z + y + 1) > 0 := by
      positivity
    have h4 : (y + 1)^2 + z^2 + 1 ≥ 2 * (y * z + y + 1) := h2
    have h5 : (y + 1)^2 + z^2 + 1 > 0 := by positivity
    apply one_div_le_one_div_of_le
    all_goals
      try linarith
  have h3 : 1 / ((z + 1)^2 + x^2 + 1) ≤ 1 / (2 * (z * x + z + 1)) := by
    have h2 : (z + 1) ^ 2 + x ^ 2 + 1 ≥ 2 * (z * x + z + 1) := by
      nlinarith [sq_nonneg (z - x), sq_nonneg (x - z)]
    have h3 : 2 * (z * x + z + 1) > 0 := by
      positivity
    have h4 : (z + 1)^2 + x^2 + 1 ≥ 2 * (z * x + z + 1) := h2
    have h5 : (z + 1)^2 + x^2 + 1 > 0 := by positivity
    apply one_div_le_one_div_of_le
    all_goals
      try linarith

  have h4 : 1 / (2 * (x * y + x + 1)) + 1 / (2 * (y * z + y + 1)) + 1 / (2 * (z * x + z + 1)) = 1 / 2 := by
    have h8 : 1 / (x * y + x + 1) + 1 / (y * z + y + 1) + 1 / (z * x + z + 1) = 1 := by
      have h6 : 1 / (x * y + x + 1) + 1 / (y * z + y + 1) + 1 / (z * x + z + 1) =
          ((y * z + y + 1) * (z * x + z + 1) + (x * y + x + 1) * (z * x + z + 1) + (x * y + x + 1) * (y * z + y + 1)) / ((x * y + x + 1) * (y * z + y + 1) * (z * x + z + 1)) := by
        field_simp
        <;> ring
      rw [h6]
      have h7 : (y * z + y + 1) * (z * x + z + 1) + (x * y + x + 1) * (z * x + z + 1) + (x * y + x + 1) * (y * z + y + 1) = (x * y + x + 1) * (y * z + y + 1) * (z * x + z + 1) := by
        have h7 : x * y * z = 1 := hxyz
        nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1), sq_nonneg (x * y * z - 1), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      rw [h7]
      field_simp
      all_goals nlinarith
    have h5 : 1 / (2 * (x * y + x + 1)) + 1 / (2 * (y * z + y + 1)) + 1 / (2 * (z * x + z + 1)) = (1 / 2) * (1 / (x * y + x + 1) + 1 / (y * z + y + 1) + 1 / (z * x + z + 1) ) := by
      field_simp
      ring
    rw [h5]
    rw [h8]
    all_goals norm_num

  linarith