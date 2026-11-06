import Mathlib

open Real Set
open scoped Real

theorem algebra_186209 (α : ℝ) (h : tan α = 0.2) :
    5 / (6 + 7 * sin (2 * α)) = 65 / 113 := by
  have h1 : sin α ≠ 0 := by 
    by_contra h2
    have htan : tan α = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h2]
    rw [htan] at h
    norm_num at h
  have h2 : cos α ≠ 0 := by 
    by_contra h2
    have htan : tan α = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h2]
    rw [htan] at h
    norm_num at h
  have htan : tan α = sin α / cos α := by
    rw [tan_eq_sin_div_cos]
  rw [htan] at h
  have h3 : sin α = 0.2 * cos α := by
    have h4 : cos α ≠ 0 := h2
    field_simp [h4] at h ⊢
    linarith
  have h4 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  rw [show sin α = 0.2 * cos α by linarith [h3]] at h4
  have h5 : cos α ^ 2 = 25 / 26 := by 
    ring_nf at h4 ⊢
    nlinarith
  have hsin2α : sin (2 * α) = 5 / 13 := by 
    rw [sin_two_mul]
    rw [show sin α = 0.2 * cos α by linarith [h3]]
    have hcos2 : cos α ^ 2 = 25 / 26 := h5
    nlinarith [sq_nonneg (cos α)]
  rw [hsin2α]
  norm_num