import Mathlib

open Real Set
open scoped Real

theorem inequalities_235205 (α β : ℝ) :
  cos α ^ 2 + cos β ^ 2 ≤ 1 + abs (cos α * cos β) := by
  cases abs_cases (cos α * cos β) with
  | inl h =>
    nlinarith [sq_nonneg (cos α - cos β), sq_nonneg (cos α + cos β), Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β, sq_nonneg (sin α - sin β), sq_nonneg (sin α + sin β)]
  | inr h =>
    nlinarith [sq_nonneg (cos α - cos β), sq_nonneg (cos α + cos β), Real.cos_sq_add_sin_sq α, Real.cos_sq_add_sin_sq β, sq_nonneg (sin α - sin β), sq_nonneg (sin α + sin β)]