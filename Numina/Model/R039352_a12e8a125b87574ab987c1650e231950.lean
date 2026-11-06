import Mathlib

open Real Set
open scoped Real

theorem algebra_13443 {x : ℝ} (hx : tan x = sqrt 5 / 2) :
    cos (2 * x) + sin (2 * x) = (4 * sqrt 5 - 1) / 9 := by

  have htan : sin x ≠ 0 := by 
    by_contra h
    have htan : tan x = 0 := by 
      rw [tan_eq_sin_div_cos]
      simp [h]
    rw [htan] at hx 
    have h1 : sqrt 5 = 0 := by linarith 
    have h2 : sqrt 5 > 0 := by 
      apply Real.sqrt_pos.mpr 
      all_goals norm_num 
    nlinarith

  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  by_cases hcos : cos x = 0

  · -- Case cos x = 0
    have hcos0 : cos x = 0 := hcos
    have h1' : sin x ^ 2 = 1 := by 
      have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
      rw [hcos0] at h1 
      nlinarith 
    have h7 : sqrt 5 > 0 := by 
      apply Real.sqrt_pos.mpr 
      all_goals norm_num 
    have h8 : sqrt 5 ≠ 0 := by 
      linarith 
    have h10 : (0 : ℝ) = sqrt 5 / 2 := by 
      have htan0 : tan x = 0 := by 
        rw [tan_eq_sin_div_cos]
        simp [hcos0]
      linarith [htan0, hx] 
    have h11 : sqrt 5 = 0 := by 
      nlinarith 
    contradiction

  · -- Case cos x ≠ 0 
    have hcosne0 : cos x ≠ 0 := by 
      intro h 
      apply hcos 
      linarith

    have htan2 : sin x = sqrt 5 / 2 * cos x := by 
      have h1 : sin x / cos x = sqrt 5 / 2 := by 
        have htan : tan x = sin x / cos x := by 
          rw [tan_eq_sin_div_cos]
        rw [htan] at hx 
        linarith 
      have hne : cos x ≠ 0 := hcosne0 
      field_simp [hne] at h1 ⊢ 
      linarith 

    have h2 : cos x ^ 2 = 4 / 9 := by 
      have eq1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
      rw [show sin x = sqrt 5 / 2 * cos x by linarith [htan2] ] at eq1 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num) ]

    have hcos2x : cos (2 * x) = 2 * cos x ^ 2 - 1 := by 
      rw [cos_two_mul] 
    have hcos2x_val : cos (2 * x) = -1 / 9 := by 
      rw [hcos2x] 
      nlinarith [h2]

    have hsin2x : sin (2 * x) = 2 * sin x * cos x := by 
      rw [sin_two_mul] 
    have hsin2x_val : sin (2 * x) = 4 * sqrt 5 / 9 := by 
      rw [hsin2x] 
      rw [show sin x = sqrt 5 / 2 * cos x by linarith [htan2] ] 
      have h6 : cos x ^ 2 = 4 / 9 := h2 
      nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num) ]

    linarith [hcos2x_val, hsin2x_val]