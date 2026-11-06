import Mathlib

theorem algebra_163194 (α : ℝ) : 3 - 4 * Real.cos (4 * α) + Real.cos (8 * α) - 8 * (Real.cos (2 * α))^4 = -8 * Real.cos (4 * α) := by
  have h1 : Real.cos (8 * α) = 2 * (Real.cos (4 * α)) ^ 2 - 1 := by 
    rw [show 8 * α = 2 * (4 * α) by ring]
    rw [Real.cos_two_mul]
  
  have h2 : (Real.cos (2 * α)) ^ 2 = (1 + Real.cos (4 * α)) / 2 := by
    have h21 : Real.cos (4 * α) = 2 * (Real.cos (2 * α)) ^ 2 - 1 := by 
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [Real.cos_two_mul]
    linarith
  
  have h3 : (Real.cos (2 * α)) ^ 4 = ((1 + Real.cos (4 * α)) / 2) ^ 2 := by
    calc 
      (Real.cos (2 * α)) ^ 4 = ((Real.cos (2 * α)) ^ 2) ^ 2 := by ring
      _ = (( (1 + Real.cos (4 * α)) / 2 ) ^ 2) := by rw [h2]

  rw [h1, h3]
  nlinarith [Real.cos_sq_add_sin_sq (2 * α), Real.cos_sq_add_sin_sq (4 * α), Real.cos_sq_add_sin_sq (8 * α), sq_nonneg (Real.cos (4 * α)), sq_nonneg (Real.cos (2 * α)), sq_nonneg (Real.sin (2 * α)), sq_nonneg (Real.sin (4 * α)), sq_nonneg (Real.sin (8 * α)), Real.sin_sq_add_cos_sq (2 * α), Real.sin_sq_add_cos_sq (4 * α), Real.sin_sq_add_cos_sq (8 * α)]