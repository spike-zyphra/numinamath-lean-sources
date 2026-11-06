import Mathlib

open Real Set
open scoped Real

theorem algebra_244283 (x : ℝ) (hx : x ≠ 0) (h : 1 / tan (x / 2) = 1 / 2) :
    sin x / (2 - 3 * cos x) = 4 / 19 := by

  have htan : tan (x / 2) = 2 := by
    have htan' : tan (x / 2) ≠ 0 := by 
      by_contra h1
      have htan0 : tan (x / 2) = 0 := by linarith
      rw [htan0] at h
      field_simp at h 
      all_goals linarith
    field_simp [htan'] at h ⊢
    linarith

  have h1 : sin (x / 2) = 2 * cos (x / 2) := by 
    have htan2 : tan (x / 2) = 2 := htan
    rw [tan_eq_sin_div_cos] at htan2
    have hcosne : cos (x / 2) ≠ 0 := by
      by_contra h0
      rw [h0] at htan2
      norm_num at htan2
    field_simp [hcosne] at htan2 ⊢
    linarith

  have h2 : sin (x / 2) ^ 2 + cos (x / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (x / 2)
  have h3 : cos (x / 2) ^ 2 = 1 / 5 := by
    have h4 : sin (x / 2) = 2 * cos (x / 2) := h1
    rw [h4] at h2
    nlinarith
  
  have hsin : sin x = 4 / 5 := by
    have h4 : sin x = 2 * sin (x / 2) * cos (x / 2) := by 
      rw [←sin_two_mul]
      <;> ring_nf
    rw [h4]
    rw [show sin (x / 2) = 2 * cos (x / 2) by linarith [h1]]
    have h5 : cos (x / 2) ^ 2 = 1 / 5 := h3
    nlinarith [show cos (x / 2) ^ 2 = 1 / 5 from h5]

  have hcos : cos x = -3 / 5 := by 
    have h5 : cos x = 2 * cos (x / 2) ^ 2 - 1 := by 
      rw [←cos_two_mul]
      <;> ring_nf
    rw [h5]
    linarith [h3]

  have h7 : (2 - 3 * cos x) ≠ 0 := by 
    rw [hcos]
    norm_num

  rw [hsin, hcos]
  all_goals norm_num