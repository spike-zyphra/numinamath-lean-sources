import Mathlib

open Real Set
open scoped Real

theorem algebra_164651 (α : ℝ) (h : tan α = 3) :
    (2 * sin (2 * α) - 3 * cos (2 * α)) / (4 * sin (2 * α) + 5 * cos (2 * α)) = -9 / 4 := by
  have h1 : sin α ≠ 0 := by
    by_contra h2
    have htan : tan α = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h2]
      all_goals linarith
    rw [htan] at h
    all_goals linarith

  have h2 : cos α ≠ 0 := by
    by_contra h3
    have htan : tan α = 0 := by
      rw [tan_eq_sin_div_cos]
      field_simp [h3]
      all_goals linarith
    rw [htan] at h
    all_goals linarith

  have h3 : sin α = 3 * cos α := by
    have htan : tan α = sin α / cos α := by rw [tan_eq_sin_div_cos]
    rw [htan] at h
    have : sin α = 3 * cos α := by
      field_simp [h2] at h ⊢
      linarith
    exact this

  have h4 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α

  have h5 : cos α ^ 2 = 1 / 10 := by
    have h6 : sin α ^ 2 = 9 * cos α ^ 2 := by
      rw [h3]
      nlinarith
    nlinarith [h4, h6]

  have hsin2 : sin (2 * α) = 3 / 5 := by
    rw [sin_two_mul]
    rw [h3]
    have h7 : cos α ^ 2 = 1 / 10 := h5
    nlinarith [h7]

  have hcos2 : cos (2 * α) = -4 / 5 := by
    rw [cos_two_mul]
    have h7 : cos α ^ 2 = 1 / 10 := h5
    nlinarith [h7]

  have h6 : 2 * sin (2 * α) - 3 * cos (2 * α) = 18 / 5 := by
    rw [hsin2, hcos2]
    nlinarith

  have h7 : 4 * sin (2 * α) + 5 * cos (2 * α) = -8 / 5 := by
    rw [hsin2, hcos2]
    nlinarith

  rw [h6, h7]
  all_goals norm_num