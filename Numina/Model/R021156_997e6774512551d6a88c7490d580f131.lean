import Mathlib

theorem algebra_327675 (α β : ℝ) (h : Real.sin α * Real.cos β = 1) : Real.cos α * Real.sin β = 0 := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  have h3 : Real.sin α ^ 2 * Real.cos β ^ 2 = 1 := by
    have h4 : Real.sin α * Real.cos β = 1 := h
    have h5 : (Real.sin α * Real.cos β) ^ 2 = 1 ^ 2 := by
      rw [h4]
    have h6 : (Real.sin α * Real.cos β) ^ 2 = Real.sin α ^ 2 * Real.cos β ^ 2 := by
      ring
    rw [h6] at h5
    norm_num at h5 ⊢
    linarith
  have h4 : Real.sin α ^ 2 = 1 := by
    nlinarith [sq_nonneg (Real.sin α ^ 2 - 1), sq_nonneg (Real.cos β ^ 2 - 1), 
        sq_nonneg (Real.sin α), sq_nonneg (Real.cos β), 
        h1, h2, sq_nonneg (Real.sin β ^ 2), sq_nonneg (Real.cos α ^ 2)]
  have h5 : Real.cos α ^ 2 = 0 := by
    nlinarith [h1, h4]
  have h6 : Real.cos α = 0 := by
    nlinarith [sq_nonneg (Real.cos α), h5]
  simp [h6]