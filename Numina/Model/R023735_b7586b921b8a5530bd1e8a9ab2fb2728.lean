import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_250409 (x : ℝ) :
  abs (sin x) + abs (cos x) ≥ 1 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : abs (sin x) ^ 2 + abs (cos x) ^ 2 = 1 := by
    have h3 : abs (sin x) ^ 2 = sin x ^ 2 := by
      simp [abs_pow]
    have h4 : abs (cos x) ^ 2 = cos x ^ 2 := by
      simp [abs_pow]
    rw [h3, h4]
    linarith [h1]
  have h3 : (abs (sin x) + abs (cos x)) ^ 2 ≥ 1 := by
    have h4 : (abs (sin x) + abs (cos x)) ^ 2 = abs (sin x) ^ 2 + abs (cos x) ^ 2 + 2 * (abs (sin x) * abs (cos x)) := by ring
    rw [h4, h2]
    have h5 : 2 * (abs (sin x) * abs (cos x)) ≥ 0 := by
      have h6 : abs (sin x) ≥ 0 := abs_nonneg (sin x)
      have h7 : abs (cos x) ≥ 0 := abs_nonneg (cos x)
      nlinarith
    linarith
  have h4 : abs (sin x) + abs (cos x) ≥ 0 := by
    apply add_nonneg
    · apply abs_nonneg
    · apply abs_nonneg
  have h5 : abs (sin x) + abs (cos x) ≥ 1 := by
    nlinarith [sq_nonneg (abs (sin x) + abs (cos x) - 1), h4]
  exact h5