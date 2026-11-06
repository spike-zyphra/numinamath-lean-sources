import Mathlib

open Real Set
open scoped Real

theorem algebra_229333 (x : ℝ) :
  (sin x ^ 6 + cos x ^ 6 - 1) ^ 3 + 27 * sin x ^ 6 * cos x ^ 6 = 0 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq x
  have h2 : sin x ^ 6 + cos x ^ 6 = 1 - 3 * (sin x ^ 2 * cos x ^ 2) := by
    have h3 : sin x ^ 6 + cos x ^ 6 = (sin x ^ 2) ^ 3 + (cos x ^ 2) ^ 3 := by 
      ring_nf
    rw [h3]
    have h4 : (sin x ^ 2) ^ 3 + (cos x ^ 2) ^ 3 = 
      (sin x ^ 2 + cos x ^ 2) ^ 3 - 3 * (sin x ^ 2 * cos x ^ 2) * (sin x ^ 2 + cos x ^ 2) := by 
      ring_nf
    rw [h4, h1]
    all_goals
      ring_nf
  have h3 : sin x ^ 6 + cos x ^ 6 - 1 = -3 * (sin x ^ 2 * cos x ^ 2) := by
    linarith [h2]
  have h4 : (sin x ^ 6 + cos x ^ 6 - 1) ^ 3 = -27 * (sin x ^ 6 * cos x ^ 6) := by
    rw [h3]
    have h5 : (-3 * (sin x ^ 2 * cos x ^ 2)) ^ 3 = -27 * (sin x ^ 6 * cos x ^ 6) := by
      ring_nf
    nlinarith
  rw [h4]
  all_goals 
    ring_nf