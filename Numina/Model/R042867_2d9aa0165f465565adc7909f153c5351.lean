import Mathlib
open Real
theorem algebra_303161 (x a : ℝ) (hne : cos x ≠ 0 ∧ cos a ≠ 0): ((sin x) ^ 2 = (sin a) ^ 2 ↔ (cos x) ^ 2 = (cos a) ^ 2) ∧ ((cos x) ^ 2 = (cos a) ^ 2 ↔ (tan x) ^ 2 = (tan a) ^ 2):= by

  constructor
  · -- Prove that $\sin^2 x = \sin^2 a \iff \cos^2 x = \cos^2 a$
    constructor
    · -- Forward: $\sin^2 x = \sin^2 a \implies \cos^2 x = \cos^2 a$
      intro h
      have h1 : sin x ^ 2 = 1 - cos x ^ 2 := by
        have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        linarith
      have h2 : sin a ^ 2 = 1 - cos a ^ 2 := by
        have h3 : sin a ^ 2 + cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
        linarith
      rw [h1, h2] at h
      have h3 : cos x ^ 2 = cos a ^ 2 := by
        linarith
      exact h3
    · -- Backward: $\cos^2 x = \cos^2 a \implies \sin^2 x = \sin^2 a$
      intro h
      have h1 : sin x ^ 2 = 1 - cos x ^ 2 := by
        have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        linarith
      have h2 : sin a ^ 2 = 1 - cos a ^ 2 := by
        have h3 : sin a ^ 2 + cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
        linarith
      rw [h1, h2]
      have h3 : cos x ^ 2 = cos a ^ 2 := by
        linarith
      linarith
  · -- Prove that $\cos^2 x = \cos^2 a \iff \tan^2 x = \tan^2 a$
    constructor
    · -- Forward: $\cos^2 x = \cos^2 a \implies \tan^2 x = \tan^2 a$
      intro h
      have htanx : tan x ^ 2 = (sin x ^ 2) / (cos x ^ 2) := by
        have htan : tan x = sin x / cos x := by
          rw [tan_eq_sin_div_cos]
        rw [htan]
        field_simp [hne.1]
      have htana : tan a ^ 2 = (sin a ^ 2) / (cos a ^ 2) := by
        have htan : tan a = sin a / cos a := by
          rw [tan_eq_sin_div_cos]
        rw [htan]
        field_simp [hne.2]
      rw [htanx, htana]
      have h1 : sin x ^ 2 = sin a ^ 2 := by
        have h2 : sin x ^ 2 = 1 - cos x ^ 2 := by
          have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
          linarith
        have h3 : sin a ^ 2 = 1 - cos a ^ 2 := by
          have h4 : sin a ^ 2 + cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
          linarith
        rw [h2, h3]
        have h4 : cos x ^ 2 = cos a ^ 2 := by
          linarith
        linarith
      have h5 : cos x ^ 2 = cos a ^ 2 := by
        linarith
      rw [h1, h5]
    · -- Backward: $\tan^2 x = \tan^2 a \implies \cos^2 x = \cos^2 a$
      intro h
      have htanx : tan x ^ 2 = (sin x ^ 2) / (cos x ^ 2) := by
        have htan : tan x = sin x / cos x := by
          rw [tan_eq_sin_div_cos]
        rw [htan]
        field_simp [hne.1]
      have htana : tan a ^ 2 = (sin a ^ 2) / (cos a ^ 2) := by
        have htan : tan a = sin a / cos a := by
          rw [tan_eq_sin_div_cos]
        rw [htan]
        field_simp [hne.2]
      rw [htanx, htana] at h
      have h1 : sin x ^ 2 * cos a ^ 2 = sin a ^ 2 * cos x ^ 2 := by 
        field_simp [(show cos x ≠ 0 by exact hne.1), (show cos a ≠ 0 by exact hne.2)] at h ⊢
        nlinarith
      have h2 : sin x ^ 2 = 1 - cos x ^ 2 := by
        have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        linarith
      have h3 : sin a ^ 2 = 1 - cos a ^ 2 := by
        have h4 : sin a ^ 2 + cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
        linarith
      rw [h2, h3] at h1
      have h4 : cos x ^ 2 = cos a ^ 2 := by
        nlinarith
      exact h4