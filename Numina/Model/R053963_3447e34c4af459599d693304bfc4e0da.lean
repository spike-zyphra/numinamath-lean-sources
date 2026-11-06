import Mathlib

theorem inequalities_100165 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + 335 * y + 335 * z) / x + (y + 335 * x + 335 * z) / y +
    (z + 335 * x + 335 * y) / z ≥ 2013 := by

  have h1 : (x + 335 * y + 335 * z) / x + (y + 335 * x + 335 * z) / y + (z + 335 * x + 335 * y) / z =
      3 + 335 * ((y / x) + (z / x) + (x / y) + (z / y) + (x / z) + (y / z)) := by
    field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
    ring

  rw [h1]

  have h2 : (y / x) + (x / y) ≥ 2 := by
    have h_pos1 : 0 < x := hx
    have h_pos2 : 0 < y := hy
    have h3 : y / x + x / y - 2 ≥ 0 := by
      have h4 : y / x + x / y - 2 = (y^2 + x^2 - 2 * x * y) / (x * y) := by
        field_simp
        ring
      rw [h4]
      have h5 : y^2 + x^2 - 2 * x * y = (x - y) ^ 2 := by ring
      rw [h5]
      have h6 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
      have h_pos3 : x * y > 0 := mul_pos h_pos1 h_pos2
      apply div_nonneg
      linarith
      all_goals linarith
    linarith

  have h3 : (z / x) + (x / z) ≥ 2 := by
    have h_pos1 : 0 < x := hx
    have h_pos3 : 0 < z := hz
    have h4 : z / x + x / z - 2 ≥ 0 := by
      have h5 : z / x + x / z - 2 = (z^2 + x^2 - 2 * x * z) / (x * z) := by
        field_simp
        ring
      rw [h5]
      have h6 : z^2 + x^2 - 2 * x * z = (x - z) ^ 2 := by ring
      rw [h6]
      have h7 : (x - z) ^ 2 ≥ 0 := sq_nonneg (x - z)
      have h_pos4 : x * z > 0 := mul_pos h_pos1 h_pos3
      apply div_nonneg
      linarith
      all_goals linarith
    linarith

  have h4 : (z / y) + (y / z) ≥ 2 := by
    have h_pos2 : 0 < y := hy
    have h_pos3 : 0 < z := hz
    have h5 : z / y + y / z - 2 ≥ 0 := by
      have h6 : z / y + y / z - 2 = (z^2 + y^2 - 2 * y * z) / (y * z) := by
        field_simp
        ring
      rw [h6]
      have h7 : z^2 + y^2 - 2 * y * z = (y - z) ^ 2 := by ring
      rw [h7]
      have h8 : (y - z) ^ 2 ≥ 0 := sq_nonneg (y - z)
      have h_pos5 : y * z > 0 := mul_pos h_pos2 h_pos3
      apply div_nonneg
      linarith
      all_goals linarith
    linarith

  have h5 : (y / x) + (z / x) + (x / y) + (z / y) + (x / z) + (y / z) ≥ 6 := by
    linarith [h2, h3, h4]

  linarith [h5]