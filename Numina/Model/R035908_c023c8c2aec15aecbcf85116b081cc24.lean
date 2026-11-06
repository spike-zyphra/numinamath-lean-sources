import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_126413 (x : ℝ) (a b : ℝ) :
  (sin x + a * cos x) * (sin x + b * cos x) ≤ 1 + ((a + b) / 2) ^ 2 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x - (a + b) / 2 * cos x + (a - b) / 2 * sin x), sq_nonneg (cos x - (a + b) / 2 * sin x), sq_nonneg (sin x + (a + b) / 2 * cos x), sq_nonneg ((a - b) * cos x + (b - a) * sin x), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x - (a + b) / 2), sq_nonneg (a - b)]