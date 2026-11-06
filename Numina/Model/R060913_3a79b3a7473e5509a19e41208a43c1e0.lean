import Mathlib

open Real Set
open scoped Real

theorem inequalities_103391 (x : ℝ) :
  1 ≤ abs (cos x - sin x) ∨ 1 ≤ abs (cos x + sin x) := by
  by_contra h
  push_neg at h

  have h1 : abs (cos x - sin x) < 1 := by linarith [h.1, h.2]
  have h2 : abs (cos x + sin x) < 1 := by linarith [h.1, h.2]

  have h3 : (cos x - sin x) ^ 2 + (cos x + sin x) ^ 2 = 2 := by
    ring_nf
    have h4 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    nlinarith [h4]

  have h4 : (cos x - sin x) ^ 2 < 1 := by
    nlinarith [abs_lt.mp h1, sq_nonneg (cos x - sin x), sq_nonneg (cos x + sin x)]

  have h5 : (cos x + sin x) ^ 2 < 1 := by
    nlinarith [abs_lt.mp h2, sq_nonneg (cos x + sin x), sq_nonneg (cos x - sin x)]

  nlinarith [h4, h5, h3]