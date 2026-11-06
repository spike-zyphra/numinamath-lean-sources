import Mathlib

theorem algebra_22056 : Real.sqrt (5 + Real.sqrt 21) + Real.sqrt (5 - Real.sqrt 21) = Real.sqrt 14 := by
  have h1 : Real.sqrt (5 + Real.sqrt 21) + Real.sqrt (5 - Real.sqrt 21) ≥ 0 := by
    positivity
  have h2 : (Real.sqrt (5 + Real.sqrt 21) + Real.sqrt (5 - Real.sqrt 21)) ^ 2 = 14 := by
    have h3 : (Real.sqrt (5 + Real.sqrt 21)) ^ 2 = 5 + Real.sqrt 21 := by
      rw [Real.sq_sqrt]
      positivity
    have h4 : (Real.sqrt (5 - Real.sqrt 21)) ^ 2 = 5 - Real.sqrt 21 := by
      rw [Real.sq_sqrt]
      have h5 : 5 - Real.sqrt 21 ≥ 0 := by
        have : Real.sqrt 21 ≤ (5 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num), sq_nonneg (5 - Real.sqrt 21)]
        nlinarith [Real.sqrt_nonneg 21]
      linarith
    have h6 : (Real.sqrt (5 + Real.sqrt 21) + Real.sqrt (5 - Real.sqrt 21)) ^ 2 =
        (Real.sqrt (5 + Real.sqrt 21)) ^ 2 + (Real.sqrt (5 - Real.sqrt 21)) ^ 2 + 2 * (Real.sqrt (5 + Real.sqrt 21) * Real.sqrt (5 - Real.sqrt 21)) := by
      ring
    have h7 : Real.sqrt (5 + Real.sqrt 21) * Real.sqrt (5 - Real.sqrt 21) = (2 : ℝ) := by
      have h8 : Real.sqrt (5 + Real.sqrt 21) * Real.sqrt (5 - Real.sqrt 21) = Real.sqrt ((5 + Real.sqrt 21) * (5 - Real.sqrt 21)) := by
        rw [← Real.sqrt_mul (by
          nlinarith [Real.sqrt_nonneg 21, Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
        )]
      rw [h8]
      have h9 : (5 + Real.sqrt 21) * (5 - Real.sqrt 21) = (4 : ℝ) := by 
        nlinarith [Real.sqrt_nonneg 21, Real.sqrt_nonneg 21, Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]
      rw [h9]
      have h10 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h10]
      all_goals linarith
    rw [h6, h3, h4, h7]
    ring_nf
    all_goals nlinarith
  have h4 : Real.sqrt 14 ≥ 0 := Real.sqrt_nonneg 14
  have h5 : (Real.sqrt 14) ^ 2 = 14 := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
  have h6 : Real.sqrt (5 + Real.sqrt 21) + Real.sqrt (5 - Real.sqrt 21) = Real.sqrt 14 := by
    nlinarith [h1, h4, h2, h5, Real.sqrt_nonneg (5 + Real.sqrt 21), Real.sqrt_nonneg (5 - Real.sqrt 21), Real.sqrt_nonneg 14]
  exact h6