import Mathlib

open Real

theorem algebra_98577 : sqrt (9 - 6 * sqrt 2) + sqrt (9 + 6 * sqrt 2) = 2 * sqrt 6 := by
  have h1 : sqrt (9 - 6 * sqrt 2) = sqrt 6 - sqrt 3 := by
    have h2 : (sqrt 6 - sqrt 3) ^ 2 = 9 - 6 * sqrt 2 := by
      have h3 : (sqrt 6 : ℝ) ^ 2 = 6 := by
        exact Real.sq_sqrt (by norm_num)
      have h4 : (sqrt 3 : ℝ) ^ 2 = 3 := by
        exact Real.sq_sqrt (by norm_num)
      have h5 : sqrt 6 * sqrt 3 = Real.sqrt 18 := by
        rw [← Real.sqrt_mul (by norm_num)]
        all_goals norm_num
      calc
        (sqrt 6 - sqrt 3 : ℝ) ^ 2 = (sqrt 6 : ℝ) ^ 2 + (sqrt 3 : ℝ) ^ 2 - 2 * (sqrt 6 * sqrt 3) := by
          ring
        _ = 6 + 3 - 2 * (Real.sqrt 18) := by
          rw [h3, h4, h5]
        _ = 9 - 6 * Real.sqrt 2 := by
          have h5 : Real.sqrt 18 = (3 : ℝ) * Real.sqrt 2 := by
            have h3 : Real.sqrt 18 = Real.sqrt 9 * Real.sqrt 2 := by
              rw [show (18 : ℝ) = 9 * 2 by norm_num]
              rw [Real.sqrt_mul (by norm_num)]
            have h5 : Real.sqrt 9 = (3 : ℝ) := by
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            rw [h5] at h3
            linarith
          rw [h5]
          all_goals ring_nf
    have h4 : 0 ≤ (sqrt 6 - sqrt 3 : ℝ) := by
      have h5 : sqrt 6 ≥ sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
      linarith
    rw [←h2]
    all_goals norm_num [h4]
  have h3 : sqrt (9 + 6 * sqrt 2) = sqrt 6 + sqrt 3 := by
    have h4 : (sqrt 6 + sqrt 3) ^ 2 = 9 + 6 * sqrt 2 := by
      have h3 : (sqrt 6 : ℝ) ^ 2 = 6 := by
        exact Real.sq_sqrt (by norm_num)
      have h4 : (sqrt 3 : ℝ) ^ 2 = 3 := by
        exact Real.sq_sqrt (by norm_num)
      have h5 : sqrt 6 * sqrt 3 = Real.sqrt 18 := by
        rw [← Real.sqrt_mul (by norm_num)]
        all_goals norm_num
      calc
        (sqrt 6 + sqrt 3 : ℝ) ^ 2 = (sqrt 6 : ℝ) ^ 2 + (sqrt 3 : ℝ) ^ 2 + 2 * (sqrt 6 * sqrt 3) := by
          ring
        _ = 6 + 3 + 2 * (Real.sqrt 18) := by
          rw [h3, h4, h5]
        _ = 9 + 6 * Real.sqrt 2 := by
          have h5 : Real.sqrt 18 = (3 : ℝ) * Real.sqrt 2 := by
            have h3 : Real.sqrt 18 = Real.sqrt 9 * Real.sqrt 2 := by
              rw [show (18 : ℝ) = 9 * 2 by norm_num]
              rw [Real.sqrt_mul (by norm_num)]
            have h5 : Real.sqrt 9 = (3 : ℝ) := by
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            rw [h5] at h3
            linarith
          rw [h5]
          all_goals ring_nf
    have h5 : 0 ≤ (sqrt 6 + sqrt 3 : ℝ) := by
      positivity
    rw [←h4]
    all_goals norm_num [h5]
  rw [h1, h3]
  linarith