import Mathlib

theorem algebra_296741 (α : ℝ) (h : 7 * Real.sin α + 24 * Real.cos α = 25) : Real.tan α = 7 / 24 := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have sin_eq : Real.sin α = (25 - 24 * Real.cos α) / 7 := by
    linarith
  rw [sin_eq] at h1
  have quad_eq : 625 * Real.cos α ^ 2 - 1200 * Real.cos α + 576 = 0 := by
    nlinarith
  have cos_eq : Real.cos α = 24 / 25 := by
    nlinarith [sq_nonneg (25 * Real.cos α - 24)]
  have sin_eq' : Real.sin α = 7 / 25 := by
    rw [cos_eq] at sin_eq
    linarith
  rw [Real.tan_eq_sin_div_cos, sin_eq', cos_eq]
  all_goals norm_num