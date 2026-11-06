import Mathlib

open Real Set
open scoped Real

theorem algebra_251014 (x : ℝ) :
  sin x ≠ 1 / cos x ∧ cos x ≠ 1 / sin x := by
  have h1 : sin x ≠ 1 / cos x := by
    by_contra h
    have h2 : cos x ≠ 0 := by
      by_contra h3
      have h4 : sin x = 1 / cos x := by linarith [h]
      rw [h3] at h4
      field_simp at h4
      all_goals nlinarith [Real.sin_sq_add_cos_sq x]
    have h4 : sin x * cos x = 1 := by
      have h5 : cos x ≠ 0 := h2
      field_simp [h5] at h ⊢
      nlinarith
    nlinarith [sq_nonneg (sin x), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), Real.sin_sq_add_cos_sq x]
  have h2 : cos x ≠ 1 / sin x := by
    by_contra h
    have h2 : sin x ≠ 0 := by
      by_contra h3
      have h4 : cos x = 1 / sin x := by linarith [h]
      rw [h3] at h4
      field_simp at h4
      all_goals nlinarith [Real.sin_sq_add_cos_sq x]
    have h4 : cos x * sin x = 1 := by
      have h5 : sin x ≠ 0 := h2
      field_simp [h5] at h ⊢
      nlinarith
    nlinarith [sq_nonneg (sin x), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), Real.sin_sq_add_cos_sq x]
  exact ⟨h1, h2⟩