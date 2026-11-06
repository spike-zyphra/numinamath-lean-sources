import Mathlib

open Real Set
open scoped Real

theorem calculus_22517 (x : ℝ) :
  1 / cos x / sin x - sin x / cos x = 1 / tan x := by 
  by_cases hcos : cos x = 0 
  · 
    have htan0 : tan x = 0 := by 
      rw [tan_eq_sin_div_cos]
      rw [hcos]
      norm_num 
    rw [htan0]
    norm_num [hcos]
  · 
    by_cases hsin : sin x = 0 
    · 
      have htan0 : tan x = 0 := by 
        rw [tan_eq_sin_div_cos]
        rw [hsin]
        norm_num 
      rw [htan0]
      norm_num [hsin, hcos]
    · 
      have htan : tan x = sin x / cos x := by 
        rw [tan_eq_sin_div_cos]
      have h2 : 1 / cos x / sin x - sin x / cos x = cos x / sin x := by 
        have h6 : sin x ≠ 0 := by 
          intro h 
          apply hsin 
          all_goals 
            tauto 
        have h7 : cos x ≠ 0 := by 
          intro h 
          apply hcos 
          all_goals 
            tauto 
        field_simp [h7, h6]
        <;> 
        ring_nf 
        <;> 
        have h8 : cos x ^ 2 + sin x ^ 2 = 1 := by 
          exact Real.cos_sq_add_sin_sq x 
        nlinarith [Real.cos_sq_add_sin_sq x, sq_pos_of_ne_zero h7, sq_pos_of_ne_zero h6, sq_nonneg (cos x * sin x), sq_nonneg (cos x - sin x)] 
      have h5 : 1 / tan x = cos x / sin x := by 
        rw [htan]
        all_goals 
          have h6 : sin x ≠ 0 := by 
            intro h 
            apply hsin 
            all_goals 
              tauto 
          have h7 : cos x ≠ 0 := by 
            intro h 
            apply hcos 
            all_goals 
              tauto 
          field_simp [h7, h6]
      rw [h5] 
      rw [h2]
      all_goals 
        ring