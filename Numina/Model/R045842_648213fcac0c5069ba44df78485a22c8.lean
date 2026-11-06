import Mathlib

open Real

theorem algebra_188166 : 2 * sqrt (1.5 + sqrt 2) - (1.5 + sqrt 2) = 1 / 2 := by
  have h1 : sqrt (1.5 + Real.sqrt 2) = 1 + Real.sqrt 2 / 2 := by
    have h2 : (1 + Real.sqrt 2 / 2) ^ 2 = (1.5 + Real.sqrt 2 : ℝ) := by
      have h3 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
      ring_nf
      <;> rw [h3]
      <;> ring_nf
      <;> norm_num
    have h4 : 0 ≤ (1 + Real.sqrt 2 / 2 : ℝ) := by
      have h5 : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg 2
      linarith
      all_goals linarith
    rw [← h2]
    field_simp [Real.sqrt_sq, h4]
    all_goals linarith
  rw [h1]
  have h5 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (1.5 + Real.sqrt 2), Real.sqrt_nonneg (1.5 + Real.sqrt 2), h5]