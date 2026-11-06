import Mathlib

theorem algebra_301558 (α : ℝ) (h : Real.sin α - Real.cos α = 1 / 2) :
    (Real.sin α)^3 - (Real.cos α)^3 = 11 / 16 := by

  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α

  have h2 : Real.sin α * Real.cos α = 3 / 8 := by
    have eq1 : (Real.sin α - Real.cos α)^2 = (1 / 2)^2 := by
      rw [h]
    
    have eq2 : (Real.sin α - Real.cos α)^2 = Real.sin α ^ 2 - 2 * (Real.sin α * Real.cos α) + Real.cos α ^ 2 := by
      ring

    rw [eq2] at eq1

    have eq3 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := h1

    have eq4 : Real.sin α ^ 2 - 2 * (Real.sin α * Real.cos α) + Real.cos α ^ 2 = (1 / 4 : ℝ) := by
      linarith

    have eq5 : (Real.sin α ^ 2 + Real.cos α ^ 2) - 2 * (Real.sin α * Real.cos α) = 1 / 4 := by
      linarith

    rw [eq3] at eq5

    linarith

  have h3 : (Real.sin α)^3 - (Real.cos α)^3 = (Real.sin α - Real.cos α) * (Real.sin α^2 + Real.sin α * Real.cos α + Real.cos α^2) := by
    ring

  have h4 : Real.sin α^2 + Real.sin α * Real.cos α + Real.cos α^2 = 11 / 8 := by
    have h5 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := h1
    have h6 : Real.sin α * Real.cos α = 3 / 8 := h2

    calc
      Real.sin α ^ 2 + Real.sin α * Real.cos α + Real.cos α ^ 2 = (Real.sin α ^ 2 + Real.cos α ^ 2) + (Real.sin α * Real.cos α) := by
        ring
      _ = 1 + (3 / 8 : ℝ) := by 
        rw [h5, h6]
      _ = (11 / 8 : ℝ) := by 
        norm_num

  rw [h3, h]

  rw [h4]
  all_goals norm_num