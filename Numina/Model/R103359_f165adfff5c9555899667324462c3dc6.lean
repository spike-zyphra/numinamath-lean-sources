import Mathlib

theorem algebra_186255 (α : ℝ) (h : Real.sin α - Real.cos α = 1 / 2) :
    (Real.sin α) ^ 4 + (Real.cos α) ^ 4 = 23 / 32 := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : Real.sin α * Real.cos α = 3 / 8 := by
    have eq1 : (Real.sin α - Real.cos α) ^ 2 = (1 / 2) ^ 2 := by 
      rw [h]
    have eq2 : (Real.sin α - Real.cos α) ^ 2 = Real.sin α ^ 2 - 2 * (Real.sin α * Real.cos α) + Real.cos α ^ 2 := by ring
    rw [eq2] at eq1
    have eq3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := h1
    linarith
  have h3 : (Real.sin α) ^ 4 + (Real.cos α) ^ 4 = ((Real.sin α ^ 2 + Real.cos α ^ 2) ^ 2 - 2 * (Real.sin α * Real.cos α) ^ 2) := by
    ring
  rw [h3, h1, h2]
  norm_num