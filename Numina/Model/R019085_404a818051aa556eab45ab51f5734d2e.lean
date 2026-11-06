import Mathlib

theorem algebra_97135 : 2 * (Real.sqrt 2 + Real.sqrt 6) / (3 * Real.sqrt (2 + Real.sqrt 3)) = 4 / 3 := by
  have h1 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 2 + Real.sqrt 6) / 2 := by
    have h2 : ((Real.sqrt 2 + Real.sqrt 6) / 2) ^ 2 = 2 + Real.sqrt 3 := by
      have h3 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h4 : (Real.sqrt 6) ^ 2 = 6 := by
        rw [Real.sq_sqrt]
        norm_num
      have h5 : Real.sqrt 2 * Real.sqrt 6 = 2 * Real.sqrt 3 := by
        have h6 : Real.sqrt 2 * Real.sqrt 6 = Real.sqrt (2 * 6) := by
          rw [← Real.sqrt_mul (by norm_num)]
        rw [h6]
        have h7 : Real.sqrt (2 * 6 : ℝ) = 2 * Real.sqrt 3 := by
          rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          <;> ring_nf <;> norm_num
        linarith [h7]
      nlinarith [h3, h4, h5]
    have h3 : (Real.sqrt 2 + Real.sqrt 6) / 2 ≥ 0 := by
      have h4 : Real.sqrt 2 ≥ 0 := by positivity
      have h5 : Real.sqrt 6 ≥ 0 := by positivity
      linarith
    rw [← h2]
    field_simp [Real.sqrt_sq, h3]
  have h3 : 3 * Real.sqrt (2 + Real.sqrt 3) = 3 * ((Real.sqrt 2 + Real.sqrt 6) / 2) := by
    rw [h1]
  have h4 : 2 * (Real.sqrt 2 + Real.sqrt 6) / (3 * Real.sqrt (2 + Real.sqrt 3)) =
      2 * (Real.sqrt 2 + Real.sqrt 6) / (3 * ((Real.sqrt 2 + Real.sqrt 6) / 2)) := by
    rw [h1]
  rw [h4]
  have h4 : Real.sqrt 2 + Real.sqrt 6 ≠ 0 := by
    have h5 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    have h6 : Real.sqrt 6 > 0 := by
      apply Real.sqrt_pos.mpr
      norm_num
    linarith
  field_simp [h4]
  <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (6 : ℝ), Real.sqrt_nonneg (3 : ℝ)]