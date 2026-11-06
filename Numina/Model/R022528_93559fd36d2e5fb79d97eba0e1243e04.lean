import Mathlib
open Real

theorem algebra_9813 {x : ℝ} (hx : tan x = √5 / 2) :
    1 + sin (2 * x) = (9 + 4 * √5) / 9 := by

  have h1 : cos x ≠ 0 := by 
    by_contra h
    have htan : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h]
    have h3 : tan x = (0 : ℝ) := htan 
    have eq1 : (√5 / (2 : ℝ)) = (0 : ℝ) := by
      linarith [h3, hx]
    have h4 : √5 = (0 : ℝ) := by
      field_simp at eq1 ⊢
      all_goals linarith [eq1]
    have h5 : (5 : ℝ) = (0 : ℝ) := by 
      calc
        (5 : ℝ) = (√5) ^ 2 := by 
          rw [Real.sq_sqrt]
          all_goals linarith
        _ = (0 : ℝ) ^ 2 := by 
          rw [h4]
        _ = (0 : ℝ) := by 
          norm_num
    linarith
  
  -- From tan x = √5 / 2, we have sin x / cos x = √5 / 2
  have h2 : sin x = (√5 / 2) * cos x := by
    have htan : tan x = sin x / cos x := by 
      rw [tan_eq_sin_div_cos]
    rw [htan] at hx
    have hne : cos x ≠ 0 := h1
    field_simp [hne] at hx ⊢
    linarith
  
  have h3 : cos x ^ 2 = 4 / 9 := by
    have h11 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    rw [show sin x = (√5 / 2) * cos x by linarith [h2]] at h11
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  
  have h4 : sin (2 * x) = 4 * √5 / 9 := by
    have h5 : sin (2 * x) = 2 * sin x * cos x := by
      rw [sin_two_mul]
    rw [h5]
    rw [show sin x = (√5 / 2) * cos x by linarith [h2]]
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  
  linarith [h4]