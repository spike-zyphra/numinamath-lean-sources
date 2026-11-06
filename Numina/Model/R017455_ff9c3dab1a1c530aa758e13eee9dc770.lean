import Mathlib

theorem algebra_254713 (α β : ℝ) (h : Real.sin α * Real.cos β = -1 / 2) :
    Real.cos α * Real.sin β ∈ Set.Icc (-1 / 2) (1 / 2) := by
  have h1 : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : Real.sin β ^ 2 + Real.cos β ^ 2 = 1 := Real.sin_sq_add_cos_sq β
  constructor
  · -- Show that -1/2 ≤ Real.cos α * Real.sin β
    nlinarith [sq_nonneg (Real.sin α - Real.cos β), sq_nonneg (Real.cos α + Real.sin β), sq_nonneg (Real.sin α + Real.cos β), sq_nonneg (Real.sin β - Real.cos α), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β)]
  · -- Show that Real.cos α * Real.sin β ≤ 1/2
    nlinarith [sq_nonneg (Real.sin α - Real.cos β), sq_nonneg (Real.cos α + Real.sin β), sq_nonneg (Real.sin α + Real.cos β), sq_nonneg (Real.sin β - Real.cos α), Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β, sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β)]