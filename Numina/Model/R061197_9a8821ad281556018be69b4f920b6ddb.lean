import Mathlib

theorem algebra_302802 (α : ℝ) (h : Real.sin α - Real.cos α = 1 / 3) :
    Real.sin (3 * α) + Real.cos (3 * α) = -25 / 27 := by

  have h1 : Real.sin (3 * α) = 3 * Real.sin α - 4 * Real.sin α ^ 3 := by 
    rw [Real.sin_three_mul]

  have h2 : Real.cos (3 * α) = 4 * Real.cos α ^ 3 - 3 * Real.cos α := by 
    rw [Real.cos_three_mul]

  have h3 : Real.sin (3 * α) + Real.cos (3 * α) = 3 * (Real.sin α - Real.cos α) + 4 * (Real.cos α ^ 3 - Real.sin α ^ 3) := by 
    rw [h1, h2]
    ring

  rw [h3, h]

  have h4 : Real.sin α * Real.cos α = 4 / 9 := by
    have h5 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    have h6 : (Real.sin α - Real.cos α) ^ 2 = 1 / 9 := by
      rw [h]
      all_goals norm_num
    have h7 : (Real.sin α - Real.cos α) ^ 2 = Real.sin α ^ 2 + Real.cos α ^ 2 - 2 * (Real.sin α * Real.cos α) := by
      ring
    rw [h7] at h6
    have h8 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α 
    have h9 : 1 - 2 * (Real.sin α * Real.cos α) = 1 / 9 := by 
      linarith [h5, h6]
    linarith

  have h5 : Real.cos α ^ 3 - Real.sin α ^ 3 = -13 / 27 := by
    have h7 : Real.cos α ^ 3 - Real.sin α ^ 3 = (Real.cos α - Real.sin α) * (Real.cos α ^ 2 + Real.sin α * Real.cos α + Real.sin α ^ 2) := by 
      ring
    rw [h7]

    have h8 : Real.cos α - Real.sin α = -1 / 3 := by
      have h9 : Real.sin α - Real.cos α = 1 / 3 := h
      linarith

    rw [h8]

    have h9 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α

    have h10 : Real.cos α ^ 2 + Real.sin α ^ 2 + Real.sin α * Real.cos α = 13 / 9 := by
      nlinarith [h4, h9]

    nlinarith [h10, h4, h9]

  have h10 : 4 * (Real.cos α ^ 3 - Real.sin α ^ 3) = -52 / 27 := by 
    linarith [h5]

  linarith [h10, Real.sin_sq_add_cos_sq α]