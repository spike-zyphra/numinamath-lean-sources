import Mathlib

open Real Set
open scoped Real

theorem inequalities_196434 (x : ℝ) :
  (sin x + 2 * cos (2 * x)) * (2 * sin (2 * x) - cos x) < 4.5 := by 
  nlinarith [sq_nonneg (sin x - sin (2 * x)), sq_nonneg (cos x - cos (2 * x)),
          sq_nonneg (sin x + sin (2 * x)), sq_nonneg (cos x + cos (2 * x)),
          Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq (2 * x),
          sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x),
          sq_nonneg (sin (2 * x) - cos (2 * x)), sq_nonneg (sin (2 * x) + cos (2 * x)),
          sq_nonneg (sin (2 * x) - sin x), sq_nonneg (cos (2 * x) - cos x),
          Real.sin_two_mul x, Real.sin_two_mul (x / 2), Real.cos_sq x, Real.sin_sq x, 
          Real.cos_sq (2 * x), Real.sin_sq (2 * x)]