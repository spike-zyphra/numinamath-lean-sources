import Mathlib

theorem algebra_224145 : Real.sqrt (4 + Real.sqrt 7) - Real.sqrt (4 - Real.sqrt 7) = Real.sqrt 2 := by
  have h1 : 0 ≤ Real.sqrt (4 + Real.sqrt 7) := by positivity
  have h2 : 0 ≤ Real.sqrt (4 - Real.sqrt 7) := by positivity

  have h5 : Real.sqrt (4 + Real.sqrt 7) ^ 2 = 4 + Real.sqrt 7 := by
    rw [Real.sq_sqrt]
    positivity
  have h6 : Real.sqrt (4 - Real.sqrt 7) ^ 2 = 4 - Real.sqrt 7 := by 
    rw [Real.sq_sqrt]
    have h7 : 0 ≤ (4 - Real.sqrt 7 : ℝ) := by
      have h8 : Real.sqrt 7 ≤ (4 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
      linarith [Real.sqrt_nonneg 7]
    nlinarith

  have h9 : (Real.sqrt (4 + Real.sqrt 7) - Real.sqrt (4 - Real.sqrt 7)) ^ 2 = 2 := by
    have h10 : Real.sqrt (4 + Real.sqrt 7) ^ 2 = 4 + Real.sqrt 7 := by
      rw [Real.sq_sqrt]
      positivity
    have h11 : Real.sqrt (4 - Real.sqrt 7) ^ 2 = 4 - Real.sqrt 7 := by 
      rw [Real.sq_sqrt]
      have h7 : 0 ≤ (4 - Real.sqrt 7 : ℝ) := by
        have h8 : Real.sqrt 7 ≤ (4 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
        linarith [Real.sqrt_nonneg 7]
      linarith
    have h12 : Real.sqrt (4 + Real.sqrt 7) * Real.sqrt (4 - Real.sqrt 7) = 3 := by 
      have h13 : Real.sqrt (4 + Real.sqrt 7) * Real.sqrt (4 - Real.sqrt 7) = Real.sqrt ((4 + Real.sqrt 7) * (4 - Real.sqrt 7)) := by 
        rw [← Real.sqrt_mul (by
          nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
        )]
      have h14 : (4 + Real.sqrt 7) * (4 - Real.sqrt 7) = 9 := by
        nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
      rw [h14] at h13
      rw [h13]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> nlinarith
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg (4 + Real.sqrt 7), Real.sqrt_nonneg (4 - Real.sqrt 7), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]

  have h11 : Real.sqrt (4 + Real.sqrt 7) - Real.sqrt (4 - Real.sqrt 7) ≥ 0 := by
    have h12 : Real.sqrt (4 + Real.sqrt 7) ≥ Real.sqrt (4 - Real.sqrt 7) := by
      apply Real.sqrt_le_sqrt
      nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num)]
    nlinarith [Real.sqrt_nonneg (4 - Real.sqrt 7)]

  have h10 : (Real.sqrt (4 + Real.sqrt 7) - Real.sqrt (4 - Real.sqrt 7)) ^ 2 = (Real.sqrt 2) ^ 2 := by
    rw [h9]
    rw [Real.sq_sqrt]
    all_goals norm_num

  have h14 : Real.sqrt (4 + Real.sqrt 7) - Real.sqrt (4 - Real.sqrt 7) = Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (4 + Real.sqrt 7), Real.sqrt_nonneg (4 - Real.sqrt 7), Real.sqrt_nonneg 2]
  exact h14