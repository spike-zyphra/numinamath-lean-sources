import Mathlib

open Real

theorem algebra_94962 : (2 * sqrt 6) / (sqrt 2 + sqrt 3 + sqrt 5) = sqrt 2 + sqrt 3 - sqrt 5 := by

  have h1 : sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num [Real.sqrt_nonneg]
  
  have h2 : 0 < (sqrt 2 + sqrt 3 + sqrt 5 : ℝ) := by
    positivity
  
  have h3 : (2 * sqrt 6) = (sqrt 2 + sqrt 3 - sqrt 5) * (sqrt 2 + sqrt 3 + sqrt 5) := by
    rw [h1]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (5 : ℝ), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
      sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 5)
    ]

  have h4 : (2 * sqrt 6) / (sqrt 2 + sqrt 3 + sqrt 5) = (sqrt 2 + sqrt 3 - sqrt 5) := by 
    have h5 : (sqrt 2 + sqrt 3 + sqrt 5) ≠ 0 := by
      positivity
    field_simp [h5]
    <;> nlinarith [h3, Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (5 : ℝ)]

  exact h4