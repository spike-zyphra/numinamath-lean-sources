import Mathlib

open Real Set
open scoped Real

theorem algebra_217248 (α : ℝ) (h : tan α + cot α = 4) :
    sqrt (1 / cos α ^ 2 + 1 / sin α ^ 2 - 1 / 2 * 1 / cos α * 1 / sin α) = sqrt 14 := by
  have h1 : sin α ≠ 0 := by
    by_contra h2
    have htan : tan α = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h2]
    have hcot : cot α = 0 := by
      rw [cot_eq_cos_div_sin]
      simp [h2]
    rw [htan, hcot] at h
    linarith
  have h2' : cos α ≠ 0 := by
    by_contra h3
    have htan : tan α = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h3]
    have hcot : cot α = 0 := by
      rw [cot_eq_cos_div_sin]
      simp [h3]
    rw [htan, hcot] at h
    linarith
  have h3 : sin α * cos α = 1 / 4 := by 
    have htan : tan α = sin α / cos α := by
      rw [tan_eq_sin_div_cos]
    have hcot : cot α = cos α / sin α := by 
      rw [cot_eq_cos_div_sin]
    rw [htan, hcot] at h
    field_simp [h1, h2'] at h 
    linarith [Real.sin_sq_add_cos_sq α]
  have h5 : 1 / cos α ^ 2 + 1 / sin α ^ 2 = 16 := by 
    have h7 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    have h6 : sin α ^ 2 * cos α ^ 2 = (1 / 16) := by
      calc 
        sin α ^ 2 * cos α ^ 2 = (sin α * cos α) ^ 2 := by ring
        _ = (1 / 4) ^ 2 := by
          rw [h3]
        _ = (1 / 16) := by norm_num 
    have h8 : 1 / cos α ^ 2 + 1 / sin α ^ 2 = (sin α ^ 2 + cos α ^ 2) / (sin α ^ 2 * cos α ^ 2) := by 
      field_simp [h1, h2']
      <;> ring
    rw [h8, h6, h7]
    all_goals norm_num
  have h7' : 1 / 2 * 1 / cos α * 1 / sin α = 2 := by 
    field_simp [h1, h2']
    have h4' : sin α * cos α = 1 / 4 := h3 
    linarith [h4']
  have h8 : (1 / cos α ^ 2 + 1 / sin α ^ 2 - 1 / 2 * 1 / cos α * 1 / sin α) = (14 : ℝ) := by 
    linarith [h5, h7']
  rw [h8]