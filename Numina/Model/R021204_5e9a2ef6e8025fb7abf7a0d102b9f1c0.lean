import Mathlib

theorem algebra_102165 : Real.sqrt (45 - Real.sqrt 2000) + Real.sqrt (45 + Real.sqrt 2000) = 10 := by
  have h1 : Real.sqrt 2000 ≥ 0 := by positivity
  have h2 : 45 - Real.sqrt 2000 ≥ 0 := by
    have h3 : Real.sqrt 2000 ≤ (45 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2000 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ 2000 by norm_num)]
    nlinarith
  have h3 : Real.sqrt (45 - Real.sqrt 2000) ≥ 0 := by positivity
  have h4 : Real.sqrt (45 + Real.sqrt 2000) ≥ 0 := by positivity
  have h5 : (Real.sqrt (45 - Real.sqrt 2000) + Real.sqrt (45 + Real.sqrt 2000)) ^ 2 = 100 := by
    have h6 : (Real.sqrt (45 - Real.sqrt 2000) + Real.sqrt (45 + Real.sqrt 2000)) ^ 2 =
            (Real.sqrt (45 - Real.sqrt 2000)) ^ 2 + (Real.sqrt (45 + Real.sqrt 2000)) ^ 2 + 2 * (Real.sqrt (45 - Real.sqrt 2000) * Real.sqrt (45 + Real.sqrt 2000)) := by ring
    rw [h6]
    have h7 : (Real.sqrt (45 - Real.sqrt 2000)) ^ 2 = 45 - Real.sqrt 2000 := by
      rw [Real.sq_sqrt]
      linarith
    have h8 : (Real.sqrt (45 + Real.sqrt 2000)) ^ 2 = 45 + Real.sqrt 2000 := by
      rw [Real.sq_sqrt]
      nlinarith [Real.sqrt_nonneg (2000 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ 2000 by norm_num)]
    have h9 : Real.sqrt (45 - Real.sqrt 2000) * Real.sqrt (45 + Real.sqrt 2000) = (5 : ℝ) := by
      have h10 : Real.sqrt (45 - Real.sqrt 2000) * Real.sqrt (45 + Real.sqrt 2000) = Real.sqrt ((45 - Real.sqrt 2000) * (45 + Real.sqrt 2000)) := by
        rw [← Real.sqrt_mul (by nlinarith)]
        all_goals nlinarith [Real.sqrt_nonneg ((45 - Real.sqrt 2000) * (45 + Real.sqrt 2000)), Real.sqrt_nonneg (45 - Real.sqrt 2000), Real.sqrt_nonneg (45 + Real.sqrt 2000)]
      rw [h10]
      have h11 : ((45 - Real.sqrt 2000) * (45 + Real.sqrt 2000) : ℝ) = (25 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (2000 : ℝ), Real.mul_self_sqrt (show (0 : ℝ) ≤ 2000 by norm_num)]
      rw [h11]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      all_goals try nlinarith
    nlinarith [Real.sqrt_nonneg (45 - Real.sqrt 2000), Real.sqrt_nonneg (45 + Real.sqrt 2000), h7, h8, h9]
  have h6 : Real.sqrt (45 - Real.sqrt 2000) + Real.sqrt (45 + Real.sqrt 2000) ≥ 0 := by positivity
  have h7 : Real.sqrt (45 - Real.sqrt 2000) + Real.sqrt (45 + Real.sqrt 2000) = 10 := by
    nlinarith [Real.sqrt_nonneg (45 - Real.sqrt 2000), Real.sqrt_nonneg (45 + Real.sqrt 2000), h5, h6]
  exact h7