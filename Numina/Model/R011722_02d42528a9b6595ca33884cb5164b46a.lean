import Mathlib

open Real Set
open scoped Real

theorem inequalities_153212 (x y : ℝ) :
    (cos (x - y)) ^ 2 ≤ 4 * (1 - sin x * cos y) * (1 - cos x * sin y) := by
  have h1 : cos (x - y) = cos x * cos y + sin x * sin y := by
    rw [cos_sub]
  have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h3 : sin y ^ 2 + cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  rw [h1]
  nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin y - cos y), 
    sq_nonneg (sin x + sin y), sq_nonneg (cos x + cos y), 
    sq_nonneg (sin x * cos y - cos x * sin y), 
    sq_nonneg (cos x * sin y + sin x * cos y - 1), 
    sq_nonneg (sin x * sin y - cos x * cos y), 
    mul_nonneg (show 0 ≤ sin x ^ 2 by positivity) (show 0 ≤ sin y ^ 2 by positivity), 
    mul_nonneg (show 0 ≤ sin x ^ 2 by positivity) (show 0 ≤ cos y ^ 2 by positivity), 
    mul_nonneg (show 0 ≤ cos x ^ 2 by positivity) (show 0 ≤ sin y ^ 2 by positivity), 
    mul_nonneg (show 0 ≤ cos x ^ 2 by positivity) (show 0 ≤ cos y ^ 2 by positivity)
  ]