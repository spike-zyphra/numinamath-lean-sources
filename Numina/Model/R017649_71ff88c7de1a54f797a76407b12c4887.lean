import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_150407 {x : ℝ} (hx : 0 < x) :
    x ^ logb 2 (0.25 * x ^ 3) = 512 * x ^ 4 ↔ x = 1 / 2 ∨ x = 8 := by
  constructor
  · -- Forward direction: if x^logb 2 (0.25 * x ^ 3) = 512 * x ^ 4, then x = 1/2 or 8 
    intro h_eq
    have h1 : 0 < x := hx
    have h2 : logb 2 (0.25 * x ^ 3) = -2 + 3 * logb 2 x := by
      have h3 : logb 2 (0.25 * x ^ 3) = logb 2 (0.25) + logb 2 (x ^ 3) := by 
        rw [logb_mul (by norm_num) (by positivity)]
      have h4 : logb 2 (0.25 : ℝ) = -2 := by 
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      have h5 : logb 2 (x ^ 3 : ℝ) = 3 * logb 2 x := by 
        simp [logb_pow]
      rw [h3, h4, h5]
    have h3 : logb 2 (x ^ logb 2 (0.25 * x ^ 3)) = logb 2 (512 * x ^ 4) := by 
      rw [h_eq]
    have h4 : logb 2 (x ^ logb 2 (0.25 * x ^ 3)) = logb 2 (0.25 * x ^ 3) * logb 2 x := by 
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals linarith
    have h5 : logb 2 (512 * x ^ 4) = logb 2 (512 : ℝ) + logb 2 (x ^ 4 : ℝ) := by 
      rw [logb_mul (by norm_num) (by positivity)]
    have h6 : logb 2 (512 : ℝ) = 9 := by 
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    have h7 : logb 2 (x ^ 4 : ℝ) = 4 * logb 2 x := by 
      simp [logb_pow]
    rw [h4, h5, h6, h7] at h3
    rw [h2] at h3 
    have h8 : 3 * (logb 2 x) ^ 2 - 6 * (logb 2 x) - 9 = 0 := by 
      nlinarith [h3]
    have h9 : (logb 2 x - 3) * (logb 2 x + 1) = 0 := by 
      nlinarith [h8]
    cases' (mul_eq_zero.1 h9) with h10 h11 
    · -- Case 1: $\log_2 x = 3$
      have h12 : logb 2 x = 3 := by linarith
      have h13 : x = 8 := by
        have h14 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by 
          field_simp at *
        rw [h12] at h14
        norm_num at h14 ⊢
        linarith
      right 
      linarith 
    · -- Case 2: $\log_2 x = -1$
      have h15 : logb 2 x = -1 := by linarith 
      have h16 : x = (1 / 2 : ℝ) := by 
        have h17 : x = (2 : ℝ) ^ (logb 2 x : ℝ) := by 
          field_simp at *
        rw [h15] at h17
        norm_num at h17 ⊢
        linarith
      left 
      linarith 
  · -- Backward direction: if x = 1/2 or 8, then the equation holds 
    rintro (h_eq | h_eq)
    · -- Case where x = 1/2
      rw [h_eq]
      have h1 : logb 2 (0.25 * (1 / 2 : ℝ) ^ 3) = -5 := by 
        have h3 : logb 2 (0.25 * (1 / 2 : ℝ) ^ 3) = logb 2 (0.25 : ℝ) + logb 2 ((1 / 2 : ℝ) ^ 3) := by 
          rw [logb_mul (by norm_num) (by positivity)]
        have h4 : logb 2 (0.25 : ℝ) = -2 := by 
          rw [logb_eq_iff_rpow_eq] <;> norm_num 
        have h5 : logb 2 ((1 / 2 : ℝ) ^ 3) = 3 * logb 2 (1 / 2 : ℝ) := by 
          simp [logb_pow]
        have h2 : logb 2 (1 / 2 : ℝ) = -1 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num 
        rw [h3, h4, h5, h2]
        norm_num 
      have h4 : (1 / 2 : ℝ) ^ logb 2 (0.25 * (1 / 2 : ℝ) ^ 3) = 32 := by 
        rw [show logb 2 (0.25 * (1 / 2 : ℝ) ^ 3) = -5 by linarith [h1]]
        norm_num 
      have h5 : (512 * (1 / 2 : ℝ) ^ 4 : ℝ) = 32 := by norm_num
      linarith [h4, h5] 
    · -- Case where x = 8 
      rw [h_eq]
      have h1 : logb 2 (0.25 * (8 : ℝ) ^ 3) = 7 := by 
        rw [logb_eq_iff_rpow_eq] <;> norm_num 
      have h2 : (8 : ℝ) ^ logb 2 (0.25 * 8 ^ 3) = (8 : ℝ) ^ (7 : ℝ) := by 
        rw [h1]
      have h3 : (512 * (8 : ℝ) ^ 4 : ℝ) = (8 : ℝ) ^ (7 : ℝ) := by norm_num 
      rw [h2]
      all_goals linarith [h3]