import Mathlib

open Real

theorem calculus_10745 (α β : ℝ) (h₀ : tan α = 8) (h₁ : tan β = 7) :
    tan (α - β) = 1 / 57 := by 
  have h2 : cos α ≠ 0 := by 
    by_contra h
    have htan : tan α = 0 := by 
      rw [tan_eq_sin_div_cos]
      simp [h]
    rw [htan] at h₀
    all_goals linarith
  have h3 : cos β ≠ 0 := by
    by_contra h
    have htan : tan β = 0 := by 
      rw [tan_eq_sin_div_cos]
      simp [h]
    rw [htan] at h₁
    all_goals linarith
  have h4 : sin α = 8 * cos α := by
    have htan : tan α = sin α / cos α := by 
      rw [tan_eq_sin_div_cos]
    rw [htan] at h₀
    have hcos : cos α ≠ 0 := h2
    field_simp [hcos] at h₀ ⊢
    linarith
  have h5 : sin β = 7 * cos β := by
    have htan : tan β = sin β / cos β := by 
      rw [tan_eq_sin_div_cos]
    rw [htan] at h₁
    have hcos : cos β ≠ 0 := h3
    field_simp [hcos] at h₁ ⊢
    linarith
  have htan : tan (α - β) = sin (α - β) / cos (α - β) := by 
    rw [tan_eq_sin_div_cos]
  rw [htan]
  rw [sin_sub, cos_sub]
  have h7 : sin α * cos β - cos α * sin β = cos α * cos β := by
    rw [h4, h5]
    ring_nf
  have h8 : cos α * cos β + sin α * sin β = 57 * (cos α * cos β) := by
    rw [h4, h5]
    ring_nf
  rw [h7, h8]
  have hcos1 : cos α ≠ 0 := h2
  have hcos2 : cos β ≠ 0 := h3
  field_simp [hcos1, hcos2, show cos α * cos β ≠ 0 by
    apply mul_ne_zero
    exact hcos1
    exact hcos2
  ]
  <;> norm_num
  <;> linarith [h₀, h₁, hcos1, hcos2]