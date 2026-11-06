import Mathlib

open Real Set
open scoped Real

theorem inequalities_153526 (x : ℝ) :
  1 / 2 ≤ (sin x)^4 + (cos x)^4 ∧ (sin x)^4 + (cos x)^4 ≤ 1 := by
    have h1 : (sin x)^4 + (cos x)^4 ≥ 1 / 2 := by
      have h2 : (sin x)^4 + (cos x)^4 = 1 - (1 / 2) * (sin (2 * x)) ^ 2 := by
        have h21 : (sin x)^4 + (cos x)^4 = ((sin x)^2 + (cos x)^2)^2 - 2 * ((sin x * cos x)^2) := by
          ring
        have h22 : (sin x)^2 + (cos x)^2 = 1 := by
          exact sin_sq_add_cos_sq x
        have h23 : sin x * cos x = (1 / 2) * sin (2 * x) := by
          rw [sin_two_mul]
          all_goals linarith
        rw [h21, h22, h23]
        ring_nf
      have h3 : (sin (2 * x)) ^ 2 ≤ 1 := by
        have hsin : (sin (2 * x)) ^ 2 ≤ 1 := by
          apply sin_sq_le_one
        linarith
      linarith [h2, h3]
    
    have h2 : (sin x)^4 + (cos x)^4 ≤ 1 := by
      have h4 : (sin x)^4 + (cos x)^4 = 1 - (1 / 2) * (sin (2 * x)) ^ 2 := by
        have h41 : (sin x)^4 + (cos x)^4 = ((sin x)^2 + (cos x)^2)^2 - 2 * ((sin x * cos x)^2) := by
          ring
        have h42 : (sin x)^2 + (cos x)^2 = 1 := by
          exact sin_sq_add_cos_sq x
        have h43 : sin x * cos x = (1 / 2) * sin (2 * x) := by
          rw [sin_two_mul]
          all_goals linarith
        rw [h41, h42, h43]
        ring_nf
      have h5 : (sin (2 * x)) ^ 2 ≥ 0 := by
        apply sq_nonneg
      linarith [h4, h5]

    constructor
    · exact h1
    · exact h2