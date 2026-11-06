import Mathlib

theorem algebra_146189 (α : ℝ) :
    (1 + Real.sin α + Real.cos α) ^ 2 / 2 = (1 + Real.sin α) * (1 + Real.cos α) := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have eq1 : (1 + Real.sin α + Real.cos α) ^ 2 = 1 + Real.sin α ^ 2 + Real.cos α ^ 2 + 2 * Real.sin α + 2 * Real.cos α + 2 * (Real.sin α * Real.cos α) := by
    ring
  have eq2 : (1 + Real.sin α) * (1 + Real.cos α) = 1 + Real.cos α + Real.sin α + Real.sin α * Real.cos α := by
    ring

  rw [eq1]
  linarith [eq2, h1]