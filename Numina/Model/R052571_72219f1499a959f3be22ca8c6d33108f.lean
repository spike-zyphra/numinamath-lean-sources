import Mathlib

open Real Set
open scoped Real

theorem inequalities_245406 (x : ℝ) :
  2 * (sin x)^4 + 3 * (sin x)^2 * (cos x)^2 + 5 * (cos x)^4 ≤ 5 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (sin x ^ 2 - 1), sq_nonneg (cos x ^ 2 - 1),
          sq_nonneg (sin x ^ 2 - cos x ^ 2),
          sq_nonneg (sin x * cos x),
          sq_nonneg (sin x ^ 4 - cos x ^ 4),
          sq_nonneg (sin x ^ 2), sq_nonneg (cos x ^ 2),
          h1]