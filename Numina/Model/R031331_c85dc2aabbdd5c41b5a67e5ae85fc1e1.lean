import Mathlib

theorem algebra_179067 (α : ℝ) (n : ℝ) (h : Real.sin α - Real.cos α = n) :
Real.sin α ^ 3 - Real.cos α ^ 3 = (3 * n - n ^ 3) / 2 := by
  have eq1 : Real.sin α ^ 3 - Real.cos α ^ 3 = (Real.sin α - Real.cos α) * (Real.sin α ^ 2 + Real.sin α * Real.cos α + Real.cos α ^ 2) := by 
    ring
  rw [eq1, h]
  have eq2 : Real.sin α ^ 2 + Real.sin α * Real.cos α + Real.cos α ^ 2 = 1 + Real.sin α * Real.cos α := by 
    have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linarith 
  rw [eq2]
  have eq3 : Real.sin α * Real.cos α = (1 - n ^ 2) / 2 := by 
    have eq4 : (Real.sin α - Real.cos α) ^ 2 = n ^ 2 := by 
      rw [h]
    have eq5 : (Real.sin α - Real.cos α) ^ 2 = Real.sin α ^ 2 - 2 * (Real.sin α * Real.cos α) + Real.cos α ^ 2 := by 
      ring
    rw [eq5] at eq4
    have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linarith [h1, eq4]
  rw [eq3]
  ring