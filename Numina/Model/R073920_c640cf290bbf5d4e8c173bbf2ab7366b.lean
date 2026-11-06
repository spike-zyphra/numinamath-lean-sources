import Mathlib

open Real Set
open scoped Real

theorem algebra_324680 {x : ℝ} :
  (4 * sin x ^ 2 - 3) * (4 * cos x ^ 2 - 3) =
  4 * sin (2 * x) ^ 2 - 3 := by
  have h1 : sin (2 * x) = 2 * sin x * cos x := by
    rw [sin_two_mul]
  have h2 : sin (2 * x) ^ 2 = 4 * sin x ^ 2 * cos x ^ 2 := by
    rw [h1]
    ring_nf
  rw [h2]
  have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (sin x ^ 2), sq_nonneg (cos x ^ 2), Real.sin_sq_add_cos_sq x]