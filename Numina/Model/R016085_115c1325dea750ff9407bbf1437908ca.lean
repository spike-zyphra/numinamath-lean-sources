import Mathlib

theorem algebra_13085 (α β : ℝ) (h₁ : Real.sin α / Real.sin β = 2017) (h₂ : Real.cos β / Real.cos α = 311) :
    Real.sin (2 * α) / Real.sin (2 * β) = 6 + 151 / 311 := by

  have h3 : Real.sin β ≠ 0 := by
    by_contra h
    have : Real.sin α / Real.sin β = 0 := by
      rw [h]
      norm_num
    linarith

  have h4 : Real.cos α ≠ 0 := by
    by_contra h
    have : Real.cos β / Real.cos α = 0 := by 
      rw [h]
      norm_num
    linarith

  have h5 : Real.sin α = 2017 * Real.sin β := by
    have h6 : Real.sin β ≠ 0 := h3
    field_simp [h6] at h₁
    linarith

  have h7 : Real.cos β = 311 * Real.cos α := by 
    have h8 : Real.cos α ≠ 0 := h4
    field_simp [h8] at h₂
    linarith

  have h8 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
    rw [Real.sin_two_mul]

  have h9 : Real.sin (2 * β) = 2 * Real.sin β * Real.cos β := by 
    rw [Real.sin_two_mul]

  rw [h8, h9]

  have h10 : Real.sin α = 2017 * Real.sin β := h5
  have h11 : Real.cos β = 311 * Real.cos α := h7

  have h15 : Real.sin α / Real.sin β = (2017 : ℝ) := by 
    have h6 : Real.sin β ≠ 0 := h3
    field_simp [h6] at h₁ ⊢
    linarith

  have h16 : Real.cos α / Real.cos β = (1 / 311 : ℝ) := by 
    have h17 : Real.cos β = 311 * Real.cos α := h7
    have h18 : Real.cos α ≠ 0 := h4
    have h19 : Real.cos β ≠ 0 := by 
      by_contra h
      have h15 : Real.cos β = 0 := by linarith
      rw [h15] at h7
      have h16 : Real.cos α = 0 := by linarith
      contradiction
    rw [h17]
    field_simp [h18, h19]
    <;> nlinarith

  have h14 : (2 * Real.sin α * Real.cos α) / (2 * Real.sin β * Real.cos β) = (Real.sin α / Real.sin β) * (Real.cos α / Real.cos β) := by 
    field_simp [show Real.sin β ≠ 0 by exact h3, show Real.cos α ≠ 0 by exact h4, show Real.cos β ≠ 0 by
      by_contra h
      have h15 : Real.cos β = 0 := by linarith
      rw [h15] at h7
      have h16 : Real.cos α = 0 := by linarith
      contradiction
    ]
    <;> ring

  rw [h14, h15, h16]
  <;> norm_num