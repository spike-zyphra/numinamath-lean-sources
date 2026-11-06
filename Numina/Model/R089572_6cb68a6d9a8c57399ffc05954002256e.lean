import Mathlib

theorem algebra_164616 (α : ℝ) (h : Real.sin α - Real.cos α = n) :
    Real.sin α ^ 3 - Real.cos α ^ 3 = (3 * n - n ^ 3) / 2 := by
  have h1 : Real.sin α ^ 3 - Real.cos α ^ 3 = (Real.sin α - Real.cos α) * (Real.sin α ^ 2 + Real.sin α * Real.cos α + Real.cos α ^ 2) := by
    ring
  have h2 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h3 : Real.sin α ^ 2 + Real.sin α * Real.cos α + Real.cos α ^ 2 = 1 + Real.sin α * Real.cos α := by
    linarith [h2]
  have h4 : Real.sin α * Real.cos α = (1 - n ^ 2) / 2 := by
    have h5 : (Real.sin α - Real.cos α) ^ 2 = n ^ 2 := by
      rw [h]
    have h6 : Real.sin α ^ 2 - 2 * (Real.sin α * Real.cos α) + Real.cos α ^ 2 = n ^ 2 := by
      linarith [h5, h2]
    linarith [h6, h2]
  rw [h1, h, h3, h4]
  ring