import Mathlib

open Real Set
open scoped Real

theorem algebra_12647 (α : ℝ) (h : sin α + cos α = 1 / 5) :
    |sin α - cos α| = 7 / 5 := by
  have h1 : sin α ^ 2 + cos α ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq α
  have h2 : sin α * cos α = -12 / 25 := by
    have h3 : (sin α + cos α) ^ 2 = (1 / 5) ^ 2 := by
      rw [h]
    nlinarith [Real.sin_sq_add_cos_sq α]
  have h3 : (sin α - cos α) ^ 2 = 49 / 25 := by
    nlinarith [Real.sin_sq_add_cos_sq α, h2]
  have h4 : |sin α - cos α| = Real.sqrt ((sin α - cos α) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h4]
  rw [h3]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> linarith