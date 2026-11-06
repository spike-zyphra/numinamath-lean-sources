import Mathlib

open Real Set

theorem inequalities_221983 : IsLeast {((x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2)) +
      ((z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2)) +
      ((y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2)) | (x : ℝ) (y : ℝ) (z : ℝ)
      (_ : 0 < x) (_ : 0 < y) (_ : 0 < z)} (3/5) := by
  constructor
  · -- Show that 3/5 is in the set by using x = y = z = 1
    use 1, 1, 1, by norm_num, by norm_num, by norm_num
    norm_num
  · -- Show that no element less than 3/5 is in the set
    rintro w ⟨x, y, z, hx, hy, hz, rfl⟩
    have h1 : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
    have h2 : (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) + (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) + (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) ≥ 3 / 5 := by
      have h3 : (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) + (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) + (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) - 3 / 5 ≥ 0 := by
        have h4 : (x + y - z) ^ 2 / ((x + y) ^ 2 + z ^ 2) + (z + x - y) ^ 2 / ((z + x) ^ 2 + y ^ 2) + (y + z - x) ^ 2 / ((y + z) ^ 2 + x ^ 2) - 3 / 5 =
            (5 * ((x + y - z) ^ 2 * ((z + x) ^ 2 + y ^ 2) * ((y + z) ^ 2 + x ^ 2) +
              (z + x - y) ^ 2 * ((x + y) ^ 2 + z ^ 2) * ((y + z) ^ 2 + x ^ 2) +
              (y + z - x) ^ 2 * ((x + y) ^ 2 + z ^ 2) * ((z + x) ^ 2 + y ^ 2)) -
              3 * ((x + y) ^ 2 + z ^ 2) * ((z + x) ^ 2 + y ^ 2) * ((y + z) ^ 2 + x ^ 2)) / (5 * ((x + y) ^ 2 + z ^ 2) * ((z + x) ^ 2 + y ^ 2) * ((y + z) ^ 2 + x ^ 2)) := by
          field_simp
          ring
        rw [h4] at *
        have h5 : 0 < (5 * ((x + y) ^ 2 + z ^ 2) * ((z + x) ^ 2 + y ^ 2) * ((y + z) ^ 2 + x ^ 2)) := by
          positivity
        have h6 : (5 * ((x + y - z) ^ 2 * ((z + x) ^ 2 + y ^ 2) * ((y + z) ^ 2 + x ^ 2) +
              (z + x - y) ^ 2 * ((x + y) ^ 2 + z ^ 2) * ((y + z) ^ 2 + x ^ 2) +
              (y + z - x) ^ 2 * ((x + y) ^ 2 + z ^ 2) * ((z + x) ^ 2 + y ^ 2)) -
              3 * ((x + y) ^ 2 + z ^ 2) * ((z + x) ^ 2 + y ^ 2) * ((y + z) ^ 2 + x ^ 2)) ≥ 0 := by
          nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
          ]
        apply div_nonneg h6 (by positivity)
      linarith
    linarith