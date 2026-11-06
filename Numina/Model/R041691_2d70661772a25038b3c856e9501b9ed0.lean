import Mathlib

open Real Set
open scoped Real

theorem algebra_321107 (α β : ℝ) (h : sin α * cos β = -1/2) :
    cos α * sin β ∈ Icc (-1/2) (1/2) := by
  have h1 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : sin β ^ 2 + cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β

  have h5 : -1 / 2 ≤ cos α * sin β := by 
    nlinarith [sq_nonneg (sin α - cos β), sq_nonneg (cos α - sin β), sq_nonneg (sin α ^ 2 - cos β ^ 2), sq_nonneg (cos α ^ 2 - sin β ^ 2), sq_nonneg (sin α * sin β - cos α * cos β), sq_nonneg (sin α * cos β + cos α * sin β)]

  have h6 : cos α * sin β ≤ 1 / 2 := by 
    nlinarith [sq_nonneg (sin α - cos β), sq_nonneg (cos α - sin β), sq_nonneg (sin α ^ 2 - cos β ^ 2), sq_nonneg (cos α ^ 2 - sin β ^ 2), sq_nonneg (sin α * sin β - cos α * cos β), sq_nonneg (sin α * cos β + cos α * sin β)]

  constructor
  · linarith
  · linarith