import Mathlib

theorem algebra_227511 (α β : ℝ) (h₁ : Real.sin α + Real.sin β = 1) (h₂ : Real.cos α + Real.cos β = 0) :
    Real.cos (2 * α) + Real.cos (2 * β) = 1 := by

  have h3 : Real.cos β = - Real.cos α := by
    linarith
  have h4 : Real.sin β = 1 - Real.sin α := by
    linarith
  have h5 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h6 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  rw [h4, h3] at h6
  have h7 : Real.sin α = 1 / 2 := by
    nlinarith [h6, h5]
  have h8 : Real.sin β = 1 / 2 := by
    rw [h4]
    linarith [h7]
  have h9 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h10 : Real.cos (2 * β) = 2 * Real.cos β ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have h11 : Real.cos β = - Real.cos α := h3
  rw [h9, h10, h11]
  have h12 : Real.cos α ^ 2 = 3 / 4 := by
    have h13 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq α
    rw [show Real.sin α = 1 / 2 by linarith [h7]] at h13
    nlinarith
  nlinarith [h12]