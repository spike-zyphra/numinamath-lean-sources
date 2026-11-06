import Mathlib

theorem algebra_178604 (α : ℝ) : (Real.sin α)^6 + (Real.cos α)^6 + 3 * (Real.sin α)^2 * (Real.cos α)^2 = 1 := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by
    linarith [h1]
  have h3 : (Real.sin α) ^ 6 + (Real.cos α) ^ 6 = 1 - 3 * (Real.sin α) ^ 2 + 3 * (Real.sin α) ^ 4 := by
    have hcos : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := h2
    have h4 : (Real.cos α)^6 = (Real.cos α^2)^3 := by ring
    have h5 : (Real.sin α)^6 = (Real.sin α^2)^3 := by ring
    rw [h4, h5, hcos]
    have h6 : ((1 - Real.sin α ^ 2) : ℝ)^3 = 1 - 3 * Real.sin α ^ 2 + 3 * Real.sin α ^ 4 - Real.sin α ^ 6 := by ring
    have h7 : (Real.sin α ^ 2)^3 = Real.sin α ^ 6 := by ring
    rw [h6, h7]
    ring
  have h8 : 3 * (Real.sin α)^2 * (Real.cos α)^2 = 3 * (Real.sin α)^2 - 3 * (Real.sin α)^4 := by
    have hcos : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := h2
    rw [hcos]
    ring
  linarith [h3, h8]