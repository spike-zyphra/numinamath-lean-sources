import Mathlib

open Real

theorem algebra_4739 {x : ℝ} (hx : x = sqrt (23 - 6 * sqrt (10 + 4 * sqrt (3 - 2 * sqrt 2)))) : x = 3 - sqrt 2 := by
  have h1 : sqrt (3 - 2 * sqrt 2) = sqrt 2 - 1 := by
    have h1 : (sqrt 2 - 1) ^ 2 = 3 - 2 * sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h2 : 0 ≤ sqrt 2 - 1 := by
      have h3 : 1 < sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith [Real.sqrt_nonneg 2]
    rw [←h1]
    field_simp [Real.sqrt_sq h2]
    all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    
  have h2 : sqrt (10 + 4 * sqrt (3 - 2 * sqrt 2)) = 2 + sqrt 2 := by
    rw [h1]
    have h4 : (2 + sqrt 2) ^ 2 = 10 + 4 * (sqrt 2 - 1) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h5 : 0 ≤ (2 + sqrt 2) := by
      positivity
    rw [←h4]
    rw [Real.sqrt_sq h5]
    all_goals positivity
    all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h3 : sqrt (23 - 6 * sqrt (10 + 4 * sqrt (3 - 2 * sqrt 2))) = 3 - sqrt 2 := by
    rw [h2]
    have h4 : (3 - sqrt 2) ^ 2 = 23 - 6 * (2 + sqrt 2) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h5 : 0 ≤ (3 - sqrt 2) := by
      have h6 : sqrt 2 < 3 := by
        rw [Real.sqrt_lt] <;> norm_num
        all_goals linarith
      nlinarith
    rw [←h4]
    rw [Real.sqrt_sq h5]
    all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  rw [hx, h3]
  all_goals positivity
  all_goals nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]