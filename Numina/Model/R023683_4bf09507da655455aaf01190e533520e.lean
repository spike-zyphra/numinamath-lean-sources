import Mathlib

open Real Set
open scoped Real

theorem algebra_186201 (α : ℝ) (h : cot α = 2 / 3) :
    cos (2 * α + 7 * π / 4) = 7 * sqrt 2 / 26 := by

  have h1 : cos α ≠ 0 := by 
    by_contra hcos
    have hcot : cot α = 0 := by
      rw [cot_eq_cos_div_sin]
      simp [hcos]
    linarith [hcot, h]

  have h2 : sin α ≠ 0 := by
    by_contra hsin
    have hcot : cot α = 0 := by
      rw [cot_eq_cos_div_sin]
      simp [hsin]
    linarith [hcot, h]

  have h3 : cos α = 2 / 3 * sin α := by
    have h3 : cos α / sin α = 2 / 3 := by 
      rw [cot_eq_cos_div_sin] at h
      linarith
    have h4 : sin α ≠ 0 := h2
    field_simp [h4] at h3 ⊢
    linarith

  have h4 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α

  rw [show cos α = 2 / 3 * sin α by linarith [h3]] at h4

  have h5 : sin α ^ 2 = 9 / 13 := by
    linarith

  have h6 : cos α ^ 2 = 4 / 13 := by 
    have h7 : cos α = 2 / 3 * sin α := by linarith
    rw [h7]
    have h8 : sin α ^ 2 = 9 / 13 := h5
    nlinarith

  have h7 : cos (2 * α) = -5 / 13 := by 
    have h8 : cos (2 * α) = 2 * cos α ^ 2 - 1 := by 
      rw [cos_two_mul]
    rw [h8, show cos α ^ 2 = 4 / 13 by linarith [h6]]
    linarith

  have h8 : sin (2 * α) = 12 / 13 := by
    have h9 : sin (2 * α) = 2 * sin α * cos α := by
      rw [sin_two_mul]
    rw [h9]
    have h10 : cos α = 2 / 3 * sin α := h3
    rw [h10]
    have h11 : sin α ^ 2 = 9 / 13 := h5
    nlinarith

  have h9 : cos (7 * π / 4) = Real.sqrt 2 / 2 := by 
    have h10 : 7 * π / 4 = 2 * π - (π / 4) := by
      linarith [Real.pi_pos]
    rw [h10]
    have h11 : cos (2 * π - (π / 4)) = cos (π / 4) := by 
      rw [cos_two_pi_sub]
    rw [h11]
    have h12 : cos (π / 4) = Real.sqrt 2 / 2 := by 
      exact cos_pi_div_four
    rw [h12]

  have h10 : sin (7 * π / 4) = -Real.sqrt 2 / 2 := by
    have h11 : 7 * π / 4 = 2 * π - (π / 4) := by
      linarith [Real.pi_pos]
    rw [h11]
    have h12 : sin (2 * π - (π / 4)) = -sin (π / 4) := by
      rw [sin_two_pi_sub]
    rw [h12]
    have h13 : sin (π / 4) = Real.sqrt 2 / 2 := by
      exact sin_pi_div_four
    rw [h13]
    all_goals ring

  have h11 : cos (2 * α + 7 * π / 4) = cos (2 * α) * cos (7 * π / 4) - sin (2 * α) * sin (7 * π / 4) := by 
    rw [cos_add]

  rw [h11, h7, h9, h8, h10]

  field_simp
  <;> ring