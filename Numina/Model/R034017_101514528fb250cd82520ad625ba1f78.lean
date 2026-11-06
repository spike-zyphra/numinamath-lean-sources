import Mathlib

theorem algebra_16535 : (Real.sqrt 8 + Real.sqrt 3) / (Real.sqrt 2 + Real.sqrt 3) = Real.sqrt 6 - 1 := by
  have h1 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  have h2 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num

  rw [h1]

  have h3 : (2 * Real.sqrt 2 + Real.sqrt 3) / (Real.sqrt 2 + Real.sqrt 3) = Real.sqrt 6 - 1 := by

    have h4 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := h2
    have denominator_ne_zero : Real.sqrt 2 + Real.sqrt 3 ≠ 0 := by
      have hsqrt2_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
      have hsqrt3_pos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ)]

    field_simp [denominator_ne_zero]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (6 : ℝ), h4, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), sq_nonneg (Real.sqrt 2 - Real.sqrt 3), sq_nonneg (Real.sqrt 2 * Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (Real.sqrt 6 - 1)]
  
  linarith [h3, h2]