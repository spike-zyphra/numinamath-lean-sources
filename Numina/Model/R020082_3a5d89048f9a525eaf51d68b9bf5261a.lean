import Mathlib

open Real

theorem inequalities_248824 (α : ℝ) (hα : α > 0) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x ^ sin α ^ 2 * y ^ cos α ^ 2 < x + y := by 
  have h1 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h3 : 0 < x := hx
  have h4 : 0 < y := hy
  have h5 : sin α ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h6 : cos α ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h8 : x ^ sin α ^ 2 * y ^ cos α ^ 2 ≤ sin α ^ 2 * x + cos α ^ 2 * y := by
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      nlinarith [Real.sin_sq_add_cos_sq α, mul_pos hx hy]
  have h9 : sin α ^ 2 * x + cos α ^ 2 * y < x + y := by
    nlinarith [Real.sin_sq_add_cos_sq α, mul_pos hx hy, sq_pos_of_pos hx, sq_pos_of_pos hy]
  linarith [h8, h9]