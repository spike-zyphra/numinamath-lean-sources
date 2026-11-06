import Mathlib

theorem algebra_185528 (α : ℝ) :
    Real.cos α ^ 2 - Real.sin (2 * α) ^ 2 =
    Real.cos α ^ 2 * Real.cos (2 * α) - 2 * Real.sin α ^ 2 * Real.cos α ^ 2 := by
  have h1 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
    rw [Real.sin_two_mul]
  have h2 : Real.sin (2 * α) ^ 2 = 4 * Real.sin α ^ 2 * Real.cos α ^ 2 := by 
    rw [h1]
    ring
  have h5 : Real.cos (2 * α) = 1 - 2 * Real.sin α ^ 2 := by
    have h6 : Real.cos (2 * α) = 2 * Real.cos α ^ 2 - 1 := by 
      rw [Real.cos_two_mul]
    have h7 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by 
      linarith [Real.cos_sq_add_sin_sq α]
    rw [h7] at h6
    linarith
  rw [h2, h5]
  have h6 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  nlinarith [Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α), sq_nonneg (Real.cos α - 1), sq_nonneg (Real.cos α ^ 2 - Real.sin α ^ 2), sq_nonneg (Real.sin α * Real.cos α)]