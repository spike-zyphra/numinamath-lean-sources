import Mathlib

theorem algebra_168735 (α β : ℝ) (h₁ : Real.sin α + Real.sin β = 1) (h₂ : Real.cos α + Real.cos β = 0) :
    Real.cos (2 * α) + Real.cos (2 * β) = 1 := by
  have h3 : Real.cos β = -Real.cos α := by linarith
  have h4 : Real.sin β = 1 - Real.sin α := by linarith
  have h5 : Real.sin α = 1 / 2 := by
    have h6 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
    rw [h4, h3] at h6
    have h7 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    nlinarith [h6, h7]
  have h8 : Real.sin β = 1 / 2 := by linarith [h₁, h5]
  have h9 : Real.cos α ^ 2 = 3 / 4 := by
    have h10 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    rw [h5] at h10
    nlinarith
  have h11 : Real.cos β ^ 2 = 3 / 4 := by
    have h12 : Real.cos β = -Real.cos α := by linarith
    rw [h12]
    nlinarith [h9]
  have h13 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := Real.cos_two_mul α
  have h14 : Real.cos (2 * β) = 2 * Real.cos β ^ 2 - 1 := Real.cos_two_mul β
  rw [h13, h14]
  rw [h9, h11]
  norm_num