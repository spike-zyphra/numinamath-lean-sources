import Mathlib

open Real

theorem algebra_187382 : sqrt (3 + sqrt 8) - sqrt (3 - sqrt 8) = 2 := by
  have h1 : sqrt 8 = 2 * sqrt 2 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num [Real.sq_sqrt, mul_pow]
    <;> ring_nf <;> norm_num
  have h2 : sqrt (3 + sqrt 8) = 1 + Real.sqrt 2 := by
    rw [h1]
    have h4 : 3 + 2 * Real.sqrt 2 = (1 + Real.sqrt 2) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h4]
    have h5 : sqrt ((1 + Real.sqrt 2) ^ 2) = 1 + Real.sqrt 2 := by
      rw [Real.sqrt_sq_eq_abs]
      have h6 : 1 + Real.sqrt 2 ≥ 0 := by
        linarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
      rw [abs_of_nonneg h6]
    exact h5
  have h3 : sqrt (3 - sqrt 8) = Real.sqrt 2 - 1 := by
    rw [h1]
    have h7 : 3 - 2 * Real.sqrt 2 = (Real.sqrt 2 - 1) ^ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h7]
    have h8 : sqrt ((Real.sqrt 2 - 1) ^ 2) = Real.sqrt 2 - 1 := by
      have h9 : Real.sqrt 2 - 1 ≥ 0 := by
        have h2 : 1 < Real.sqrt (2 : ℝ) := by
          rw [Real.lt_sqrt] <;> norm_num
        linarith [h2]
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg h9]
    exact h8
  rw [h2, h3]
  linarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]