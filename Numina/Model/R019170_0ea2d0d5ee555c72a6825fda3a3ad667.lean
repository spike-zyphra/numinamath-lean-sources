import Mathlib

theorem algebra_189336 (α : ℝ) :
    Real.sin α * Real.sin (2 * α) * Real.sin (3 * α) ≠ 4 / 5 := by
  by_contra h
  have h1 : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := by 
    rw [Real.sin_two_mul]
  have h2 : Real.sin (3 * α) = 3 * Real.sin α - 4 * Real.sin α ^ 3 := by
    rw [Real.sin_three_mul]
  rw [h1, h2] at h
  have h3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h4 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h5 : Real.sin α ^ 2 ≥ 0 := by nlinarith [Real.sin_sq_add_cos_sq α]
  have h6 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by linarith [h4]
  have h7 : (2 * Real.sin α ^ 3 * Real.cos α * (3 - 4 * Real.sin α ^ 2)) ^ 2 = (4 / 5) ^ 2 := by
    have eq1 : 2 * Real.sin α ^ 3 * Real.cos α * (3 - 4 * Real.sin α ^ 2) = 4 / 5 := by
      nlinarith [h, Real.sin_sq_add_cos_sq α]
    rw [eq1]
    all_goals nlinarith
  have h8 : 4 * Real.sin α ^ 6 * (1 - Real.sin α ^ 2) * (3 - 4 * Real.sin α ^ 2) ^ 2 = (16 / 25 : ℝ) := by
    have h7' : (2 * Real.sin α ^ 3 * Real.cos α * (3 - 4 * Real.sin α ^ 2)) ^ 2 = (4 / 5) ^ 2 := h7
    have h9 : (2 * Real.sin α ^ 3 * Real.cos α * (3 - 4 * Real.sin α ^ 2)) ^ 2 = 4 * Real.sin α ^ 6 * Real.cos α ^ 2 * (3 - 4 * Real.sin α ^ 2) ^ 2 := by
      ring_nf
    rw [h9] at h7'
    rw [show Real.cos α ^ 2 = 1 - Real.sin α ^ 2 by linarith [h4]] at h7'
    nlinarith
  nlinarith [sq_nonneg (Real.sin α ^ 2 - 1 / 2), sq_nonneg (Real.sin α ^ 2 - 1 / 2), sq_nonneg (Real.sin α ^ 2 - 4 / 9), sq_nonneg (Real.sin α ^ 2 - 3 / 4), sq_nonneg (Real.sin α ^ 2 - 1 / 2), sq_nonneg (Real.sin α ^ 2 - 4 / 9), sq_nonneg (Real.sin α ^ 2 - 3 / 4), sq_nonneg (Real.sin α ^ 2 - 3 / 4), sq_nonneg ((3 - 4 * Real.sin α ^ 2) ^ 2 - 1), sq_nonneg ((3 - 4 * Real.sin α ^ 2) ^ 2 - 9), sq_nonneg (Real.sin α ^ 2 * (3 - 4 * Real.sin α ^ 2) ^ 2 - 4 / 9) ]