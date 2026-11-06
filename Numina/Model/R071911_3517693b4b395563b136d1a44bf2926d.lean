import Mathlib

open Real Set
open scoped Real

theorem algebra_313733 (α : ℝ) (h : tan α = -1 / 2) :
    (sin (2 * α) + 2 * cos (2 * α)) / (4 * cos (2 * α) - 4 * sin (2 * α)) = 1 / 14 := by

  have h1 : cos α ≠ 0 := by
    by_contra h1
    have htan : tan α = 0 := by 
      rw [tan_eq_sin_div_cos]
      simp [h1]
    rw [htan] at h
    norm_num at h
    all_goals linarith

  have h2 : sin α = -1 / 2 * cos α := by 
    rw [tan_eq_sin_div_cos] at h 
    field_simp [h1] at h 
    linarith

  have h3 : sin (2 * α) = -4 / 5 := by 
    rw [sin_two_mul]
    rw [h2]
    have hcos : cos α ^ 2 = 4 / 5 := by 
      have h4 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
      rw [h2] at h4 
      nlinarith 
    nlinarith [hcos]

  have h5 : cos (2 * α) = 3 / 5 := by 
    rw [cos_two_mul]
    have hcos : cos α ^ 2 = 4 / 5 := by 
      have h4 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
      rw [h2] at h4 
      nlinarith 
    nlinarith [hcos]

  rw [h3, h5]
  all_goals norm_num