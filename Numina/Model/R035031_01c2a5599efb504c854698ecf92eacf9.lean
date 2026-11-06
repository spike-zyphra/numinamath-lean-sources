import Mathlib

open Real

theorem inequalities_78284 (x : ℝ) (hx : 3 / 2 ≤ x ∧ x ≤ 5) :
    2 * sqrt (1 + x) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) < 2 * sqrt 19 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 1 + x ≥ 0 := by linarith
  have h2 : 2 * x - 3 ≥ 0 := by linarith
  have h3 : 15 - 3 * x ≥ 0 := by linarith
  have h4 : (2 * sqrt (1 + x) + sqrt (2 * x - 3) + sqrt (15 - 3 * x)) ^ 2 < (2 * sqrt 19) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), 
      Real.sqrt_nonneg (19 : ℝ), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x) by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x - 3) by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (15 - 3 * x) by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num), 
      sq_nonneg (sqrt (1 + x) - sqrt (2 * x - 3)), 
      sq_nonneg (sqrt (1 + x) - sqrt (15 - 3 * x)), 
      sq_nonneg (sqrt (2 * x - 3) - sqrt (15 - 3 * x)), 
      mul_nonneg (Real.sqrt_nonneg (1 + x)) (Real.sqrt_nonneg (2 * x - 3)), 
      mul_nonneg (Real.sqrt_nonneg (1 + x)) (Real.sqrt_nonneg (15 - 3 * x)), 
      mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x)), 
      Real.sqrt_nonneg (19 : ℝ), 
      sq_nonneg (x - 5), sq_nonneg (x - 3 / 2), 
      show (0 : ℝ) ≤ 5 - x by linarith, 
      show (0 : ℝ) ≤ x - 3 / 2 by linarith, 
      mul_nonneg (show (0 : ℝ) ≤ x - 3 / 2 by linarith) (show (0 : ℝ) ≤ 5 - x by linarith)
    ]
  have h5 : 0 < 2 * sqrt 19 := by
    positivity
  have h6 : 0 < 2 * sqrt (1 + x) + sqrt (2 * x - 3) + sqrt (15 - 3 * x) := by
    positivity
  nlinarith [Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x), Real.sqrt_nonneg (19 : ℝ), 
    h4, 
    Real.sq_sqrt (show (0 : ℝ) ≤ (1 + x) by linarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x - 3) by linarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (15 - 3 * x) by linarith), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (19 : ℝ) by norm_num)
  ]