import Mathlib

theorem algebra_164554 (α : ℝ) (h : Real.tan (α / 2) = 4) :
    (6 * Real.sin α - 7 * Real.cos α + 1) / (8 * Real.sin α + 9 * Real.cos α - 1) = -85 / 44 := by
  have h1 : Real.sin (α / 2) ≠ 0 := by
    by_contra h2
    have htan0 : Real.tan (α / 2) = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h2]
    linarith [h, htan0]
  have h2 : Real.cos (α / 2) ≠ 0 := by
    by_contra h2
    have htan0 : Real.tan (α / 2) = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h2]
    linarith [h, htan0]
  have h3 : Real.tan (α / 2) = Real.sin (α / 2) / Real.cos (α / 2) := by
    rw [Real.tan_eq_sin_div_cos]
  rw [h3] at h
  have h4 : Real.sin (α / 2) = 4 * Real.cos (α / 2) := by
    field_simp [h2] at h
    linarith
  have h5 : Real.sin (α / 2) ^ 2 + Real.cos (α / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α / 2)
  have h6 : Real.sin (α / 2) ^ 2 = 16 * Real.cos (α / 2) ^ 2 := by
    have h7 : Real.sin (α / 2) = 4 * Real.cos (α / 2) := h4
    rw [h7]
    ring
  have hcos2 : Real.cos (α / 2) ^ 2 = 1 / 17 := by
    have h7 : Real.sin (α / 2) ^ 2 + Real.cos (α / 2) ^ 2 = 1 := h5
    rw [h6] at h7
    linarith
  have hcos : Real.cos α = -15 / 17 := by
    have hcosα : Real.cos α = 2 * Real.cos (α / 2) ^ 2 - 1 := by 
      rw [← Real.cos_two_mul]
      ring_nf
    rw [hcosα, hcos2]
    norm_num
  have hsin : Real.sin α = 8 / 17 := by 
    have hsinα : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
      rw [← Real.sin_two_mul]
      ring_nf
    have hsin2 : Real.sin (α / 2) = 4 * Real.cos (α / 2) := h4
    rw [hsinα, hsin2]
    nlinarith [hcos2]
  rw [hsin, hcos]
  norm_num