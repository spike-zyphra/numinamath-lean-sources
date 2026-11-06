import Mathlib

theorem inequalities_112257 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    2 ≤ Real.sqrt (x / (y + z)) + Real.sqrt (y / (z + x)) + Real.sqrt (z / (x + y)) := by
  have h1 : 0 < y + z := by linarith
  have h2 : 0 < z + x := by linarith
  have h3 : 0 < x + y := by linarith
  have h4 : Real.sqrt (x / (y + z)) ≥ 2 * x / (x + y + z) := by
    have h5 : x / (y + z) ≥ (2 * x / (x + y + z)) ^ 2 := by
      have h6 : 0 < (x + y + z) := by linarith
      have h7 : 0 < (y + z) := by linarith
      have h8 : x / (y + z) - (2 * x / (x + y + z)) ^ 2 ≥ 0 := by
        have h10 : x / (y + z) - (2 * x / (x + y + z)) ^ 2 = (x * (x + y + z)^2 - 4 * x^2 * (y + z)) / ((y + z) * (x + y + z)^2) := by
          field_simp
          ring
        rw [h10]
        apply div_nonneg
        have h11 : x * (x + y + z)^2 - 4 * x^2 * (y + z) ≥ 0 := by
          nlinarith [sq_nonneg (x - (y + z)), sq_nonneg (x + y - z), sq_nonneg (x - y + z), sq_nonneg (-x + y + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
        linarith
        positivity
      linarith
    have h9 : Real.sqrt (x / (y + z)) ≥ Real.sqrt ((2 * x / (x + y + z)) ^ 2) := Real.sqrt_le_sqrt (show (2 * x / (x + y + z)) ^ 2 ≤ x / (y + z) by linarith)
    have h10 : Real.sqrt ((2 * x / (x + y + z)) ^ 2) = (2 * x / (x + y + z)) := by
      rw [Real.sqrt_sq]
      positivity
    rw [h10] at h9
    linarith
  have h5 : Real.sqrt (y / (z + x)) ≥ 2 * y / (x + y + z) := by
    have h6 : y / (z + x) ≥ (2 * y / (x + y + z)) ^ 2 := by
      have h6 : 0 < (x + y + z) := by linarith
      have h7 : 0 < (z + x) := by linarith
      have h8 : y / (z + x) - (2 * y / (x + y + z)) ^ 2 ≥ 0 := by
        have h10 : y / (z + x) - (2 * y / (x + y + z)) ^ 2 = (y * (x + y + z)^2 - 4 * y^2 * (z + x)) / ((z + x) * (x + y + z)^2) := by
          field_simp
          ring
        rw [h10]
        apply div_nonneg
        have h11 : y * (x + y + z)^2 - 4 * y^2 * (z + x) ≥ 0 := by
          nlinarith [sq_nonneg (y - (z + x)), sq_nonneg (y + x - z), sq_nonneg (y - x + z), sq_nonneg (-y + x + z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
        linarith
        positivity
      linarith
    have h9 : Real.sqrt (y / (z + x)) ≥ Real.sqrt ((2 * y / (x + y + z)) ^ 2) := Real.sqrt_le_sqrt (show (2 * y / (x + y + z)) ^ 2 ≤ y / (z + x) by linarith)
    have h10 : Real.sqrt ((2 * y / (x + y + z)) ^ 2) = (2 * y / (x + y + z)) := by
      rw [Real.sqrt_sq]
      positivity
    rw [h10] at h9
    linarith
  have h6 : Real.sqrt (z / (x + y)) ≥ 2 * z / (x + y + z) := by
    have h7 : z / (x + y) ≥ (2 * z / (x + y + z)) ^ 2 := by
      have h6 : 0 < (x + y + z) := by linarith
      have h7 : 0 < (x + y) := by linarith
      have h8 : z / (x + y) - (2 * z / (x + y + z)) ^ 2 ≥ 0 := by
        have h10 : z / (x + y) - (2 * z / (x + y + z)) ^ 2 = (z * (x + y + z)^2 - 4 * z^2 * (x + y)) / ((x + y) * (x + y + z)^2) := by
          field_simp
          ring
        rw [h10]
        apply div_nonneg
        have h11 : z * (x + y + z)^2 - 4 * z^2 * (x + y) ≥ 0 := by
          nlinarith [sq_nonneg (z - (x + y)), sq_nonneg (z + x - y), sq_nonneg (z - x + y), sq_nonneg (-z + x + y), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
        linarith
        positivity
      linarith
    have h9 : Real.sqrt (z / (x + y)) ≥ Real.sqrt ((2 * z / (x + y + z)) ^ 2) := Real.sqrt_le_sqrt (show (2 * z / (x + y + z)) ^ 2 ≤ z / (x + y) by linarith)
    have h10 : Real.sqrt ((2 * z / (x + y + z)) ^ 2) = (2 * z / (x + y + z)) := by
      rw [Real.sqrt_sq]
      positivity
    rw [h10] at h9
    linarith
  have h7 : Real.sqrt (x / (y + z)) + Real.sqrt (y / (z + x)) + Real.sqrt (z / (x + y)) ≥ 2 * x / (x + y + z) + 2 * y / (x + y + z) + 2 * z / (x + y + z) := by
    linarith [h4, h5, h6]
  have h8 : 2 * x / (x + y + z) + 2 * y / (x + y + z) + 2 * z / (x + y + z) = 2 := by
    field_simp
    <;> nlinarith
  linarith [h7, h8]