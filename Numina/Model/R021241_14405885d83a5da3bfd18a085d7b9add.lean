import Mathlib

open Real Set
open scoped Real

theorem inequalities_243000 (x : ℝ) :
  |sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))| ≤ sqrt 2 := by

  have h1 : 0 ≤ 1 + sin (2 * x) := by 
    linarith [neg_one_le_sin (2 * x), sin_le_one (2 * x)]
  
  have h2 : 0 ≤ 1 - sin (2 * x) := by 
    linarith [neg_one_le_sin (2 * x), sin_le_one (2 * x)]
  
  have h3 : sqrt (1 + sin (2 * x)) = abs (cos x + sin x) := by 
    have h4 : (1 + sin (2 * x)) = (cos x + sin x) ^ 2 := by 
      have h5 : sin (2 * x) = 2 * sin x * cos x := by 
        rw [sin_two_mul]
      rw [h5]
      have h6 : cos x ^ 2 + sin x ^ 2 = 1 := by 
        exact cos_sq_add_sin_sq x
      nlinarith [sq_nonneg (cos x + sin x), sq_nonneg (cos x - sin x)]
    rw [h4]
    have h7 : sqrt ((cos x + sin x) ^ 2) = abs (cos x + sin x) := by 
      rw [Real.sqrt_sq_eq_abs]
    exact h7
  
  have h4 : sqrt (1 - sin (2 * x)) = abs (cos x - sin x) := by 
    have h5 : (1 - sin (2 * x)) = (cos x - sin x) ^ 2 := by 
      have h6 : sin (2 * x) = 2 * sin x * cos x := by 
        rw [sin_two_mul]
      rw [h6]
      have h7 : cos x ^ 2 + sin x ^ 2 = 1 := by 
        exact cos_sq_add_sin_sq x
      nlinarith [sq_nonneg (cos x + sin x), sq_nonneg (cos x - sin x)]
    rw [h5]
    have h8 : sqrt ((cos x - sin x) ^ 2) = abs (cos x - sin x) := by 
      rw [Real.sqrt_sq_eq_abs]
    exact h8
  
  have h4' : sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x)) = abs (cos x + sin x) - abs (cos x - sin x) := by 
    rw [h3, h4]

  have eq1 : |sqrt (1 + sin (2 * x)) - sqrt (1 - sin (2 * x))| = abs (abs (cos x + sin x) - abs (cos x - sin x)) := by
    rw [h4']
    all_goals 
      simp

  rw [eq1]

  have h51 : (abs (cos x + sin x) - abs (cos x - sin x)) ^ 2 ≤ (2 : ℝ) := by
    have h61 : cos x ^ 2 + sin x ^ 2 = 1 := by 
      exact Real.cos_sq_add_sin_sq x
    by_cases h11 : cos x + sin x ≥ 0
    · -- case where cos x + sin x ≥ 0
      by_cases h22 : cos x - sin x ≥ 0
      · -- case where cos x - sin x ≥ 0
        rw [abs_of_nonneg h11, abs_of_nonneg h22]
        nlinarith [sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), mul_self_nonneg (cos x - sin x), mul_self_nonneg (cos x + sin x), sq_nonneg (cos x * sin x), h61]
      · -- case where cos x - sin x < 0
        rw [abs_of_nonneg h11, abs_of_neg (not_le.mp h22)]
        nlinarith [sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), mul_self_nonneg (cos x - sin x), mul_self_nonneg (cos x + sin x), sq_nonneg (cos x * sin x), h61]
    · -- case where cos x + sin x < 0
      by_cases h22 : cos x - sin x ≥ 0
      · -- case where cos x - sin x ≥ 0
        rw [abs_of_neg (not_le.mp h11), abs_of_nonneg h22]
        nlinarith [sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), mul_self_nonneg (cos x - sin x), mul_self_nonneg (cos x + sin x), sq_nonneg (cos x * sin x), h61]
      · -- case where cos x - sin x < 0
        rw [abs_of_neg (not_le.mp h11), abs_of_neg (not_le.mp h22)]
        nlinarith [sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), mul_self_nonneg (cos x - sin x), mul_self_nonneg (cos x + sin x), sq_nonneg (cos x * sin x), h61]

  have h61 : abs (abs (cos x + sin x) - abs (cos x - sin x)) ≤ Real.sqrt 2 := by
    have h7 : (abs (cos x + sin x) - abs (cos x - sin x)) ^ 2 ≤ (2 : ℝ) := h51
    have h8 : abs (abs (cos x + sin x) - abs (cos x - sin x)) = Real.sqrt ((abs (cos x + sin x) - abs (cos x - sin x)) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h8]
    apply Real.sqrt_le_sqrt
    linarith
  
  linarith [h61]