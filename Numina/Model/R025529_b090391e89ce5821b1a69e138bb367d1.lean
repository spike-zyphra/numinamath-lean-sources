import Mathlib

open Real

theorem algebra_145184 : sqrt (3 - sqrt 5) + sqrt (3 + sqrt 5) = sqrt 10 := by
  have h1 : 0 ≤ (3 - Real.sqrt 5 : ℝ) := by
    have h2 : Real.sqrt 5 ≤ 3 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    linarith
  have h4 : 0 ≤ (3 + Real.sqrt 5 : ℝ) := by
    positivity
  have h5 : 0 ≤ Real.sqrt (3 - Real.sqrt 5) + Real.sqrt (3 + Real.sqrt 5) := by
    positivity
  have h6 : 0 ≤ Real.sqrt 10 := by
    positivity
  have h7 : (Real.sqrt (3 - Real.sqrt 5) + Real.sqrt (3 + Real.sqrt 5)) ^ 2 = (Real.sqrt 10) ^ 2 := by
    have h8 : (Real.sqrt (3 - Real.sqrt 5) + Real.sqrt (3 + Real.sqrt 5)) ^ 2 = (Real.sqrt (3 - Real.sqrt 5)) ^ 2 + (Real.sqrt (3 + Real.sqrt 5)) ^ 2 + 2 * (Real.sqrt (3 - Real.sqrt 5) * Real.sqrt (3 + Real.sqrt 5)) := by
      ring
    have h9 : (Real.sqrt (3 - Real.sqrt 5)) ^ 2 = 3 - Real.sqrt 5 := by
      rw [Real.sq_sqrt]
      linarith
    have h10 : (Real.sqrt (3 + Real.sqrt 5)) ^ 2 = 3 + Real.sqrt 5 := by
      rw [Real.sq_sqrt]
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    have h11 : Real.sqrt (3 - Real.sqrt 5) * Real.sqrt (3 + Real.sqrt 5) = (2 : ℝ) := by
      have h12 : Real.sqrt (3 - Real.sqrt 5) * Real.sqrt (3 + Real.sqrt 5) = Real.sqrt ((3 - Real.sqrt 5) * (3 + Real.sqrt 5)) := by
        rw [← Real.sqrt_mul (by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
        )]
      rw [h12]
      have h13 : (3 - Real.sqrt 5) * (3 + Real.sqrt 5) = (4 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
      rw [h13]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h8, h9, h10, h11]
    have h14 : (Real.sqrt (10 : ℝ)) ^ 2 = 10 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    nlinarith [h14]
  nlinarith [Real.sqrt_nonneg (3 - Real.sqrt 5), Real.sqrt_nonneg (3 + Real.sqrt 5), Real.sqrt_nonneg (10 : ℝ)]