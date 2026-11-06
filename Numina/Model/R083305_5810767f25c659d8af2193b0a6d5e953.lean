import Mathlib

open Real Set
open scoped Real

theorem inequalities_215772 (x : ℝ) :
  1 / 4 ≤ (cos x) ^ 6 + (sin x) ^ 6 ∧ (cos x) ^ 6 + (sin x) ^ 6 ≤ 1 := by
  have h1 : (cos x)^2 + (sin x)^2 = 1 := by
    exact Real.cos_sq_add_sin_sq x
  have h2 : (cos x)^6 + (sin x)^6 = ((cos x)^2 + (sin x)^2)^3 - 3 * ((cos x)^2 + (sin x)^2) * ((cos x)^2 * (sin x)^2) := by
    ring_nf
  rw [h1] at h2
  have eq1 : (cos x)^6 + (sin x)^6 = 1 - 3 * ((cos x)^2 * (sin x)^2) := by
    nlinarith [h2]
  have h3 : ((cos x)^2 * (sin x)^2) ≤ (1 / 4) := by
    nlinarith [sq_nonneg (cos x ^ 2 - 1 / 2), sq_nonneg (sin x ^ 2 - 1 / 2),
      Real.sin_sq_add_cos_sq x, mul_nonneg (sq_nonneg (cos x)) (sq_nonneg (sin x))]
  have h4 : (cos x)^6 + (sin x)^6 ≥ 1 / 4 := by
    nlinarith [eq1, h3, mul_nonneg (sq_nonneg (cos x)) (sq_nonneg (sin x)), sq_nonneg ((cos x)^2 - (sin x)^2), Real.sin_sq_add_cos_sq x]
  have h5 : (cos x)^6 + (sin x)^6 ≤ 1 := by
    nlinarith [eq1, h3, mul_nonneg (sq_nonneg (cos x)) (sq_nonneg (sin x)), sq_nonneg (cos x * sin x), Real.sin_sq_add_cos_sq x]
  constructor
  · linarith
  · linarith