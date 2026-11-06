import Mathlib

open Real Set
open scoped Real

theorem inequalities_265639 (x : ℝ) :
  -1/4 ≤ 5*(cos x)^2 - 5*(cos x)^4 + 5*(sin x)*(cos x) + 1 ∧
  5*(cos x)^2 - 5*(cos x)^4 + 5*(sin x)*(cos x) + 1 ≤ 19/4 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  constructor
  · -- Prove -1/4 ≤ 5*(cos x)^2 - 5*(cos x)^4 + 5*(sin x)*(cos x) + 1
    nlinarith [sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x * cos x + 1 / 2), sq_nonneg (sin x * cos x - 1 / 2), Real.sin_sq_add_cos_sq x, sq_nonneg (cos x), sq_nonneg (sin x - 1 / 2), sq_nonneg (cos x - 1 / 2)]
  · -- Prove 5*(cos x)^2 - 5*(cos x)^4 + 5*(sin x)*(cos x) + 1 ≤ 19/4
    nlinarith [sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x * cos x - 1 / 2), sq_nonneg (sin x * cos x + 1 / 2), Real.sin_sq_add_cos_sq x, sq_nonneg (cos x), sq_nonneg (sin x - 1 / 2), sq_nonneg (cos x - 1 / 2)]