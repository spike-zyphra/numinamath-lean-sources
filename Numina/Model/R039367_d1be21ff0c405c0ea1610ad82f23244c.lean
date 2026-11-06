import Mathlib

theorem algebra_162329 (α : ℝ) : (Real.cos α)^6 + (Real.sin α)^6 = (5 + 3 * Real.cos (4 * α)) / 8 := by
  have h1 : (Real.cos α)^2 + (Real.sin α)^2 = 1 := Real.cos_sq_add_sin_sq α 
  have h2 : (Real.cos α)^6 + (Real.sin α)^6 = ((Real.cos α)^2)^3 + ((Real.sin α)^2)^3 := by 
    ring
  have h3 : ((Real.cos α)^2)^3 + ((Real.sin α)^2)^3 = ((Real.cos α)^2 + (Real.sin α)^2)^3 - 3 * ((Real.cos α)^2) * ((Real.sin α)^2) * ((Real.cos α)^2 + (Real.sin α)^2) := by 
    ring 
  have h4 : Real.cos (4 * α) = 1 - 8 * (Real.sin α)^2 * (Real.cos α)^2 := by
    have h7 : Real.cos (4 * α) = 2 * (Real.cos (2 * α)) ^ 2 - 1 := by
      rw [show 4 * α = 2 * (2 * α) by ring]
      rw [Real.cos_two_mul]
    have h8 : Real.cos (2 * α) = Real.cos α ^ 2 - Real.sin α ^ 2 := by
      rw [Real.cos_two_mul]
      <;> rw [Real.sin_sq]
      <;> ring 
    rw [h8] at h7 
    have h9 : Real.sin α ^ 2 = 1 - Real.cos α ^ 2 := by
      have h10 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := by
        linarith [h1]
      linarith
    rw [h9] at h7 
    nlinarith [sq_nonneg (Real.sin α), sq_nonneg (Real.cos α - 1), Real.sin_sq_add_cos_sq α]
  rw [h2, h3, h1]
  have h5 : (1 : ℝ) - 3 * (Real.sin α)^2 * (Real.cos α)^2 = (5 + 3 * Real.cos (4 * α)) / 8 := by
    have h6 : Real.sin α ^ 2 * Real.cos α ^ 2 = (1 - Real.cos (4 * α)) / 8 := by
      nlinarith [h4, Real.sin_sq_add_cos_sq α, sq_nonneg (Real.sin α ^ 2 - 1 / 2), sq_nonneg (Real.cos α ^ 2 - 1 / 2)]
    nlinarith 
  linarith [h5]