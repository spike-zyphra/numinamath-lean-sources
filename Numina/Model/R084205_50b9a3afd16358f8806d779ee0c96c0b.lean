import Mathlib

open Real Set
open scoped Real

theorem inequalities_171918 (a : ℝ) :
  (∀ x : ℝ, (sin x)^2 + a * cos x + a^2 ≥ 1 + cos x) ↔ a ≥ 1 ∨ a ≤ -2 := by
  constructor
  · -- Assume inequality holds, show a ≥ 1 or a ≤ -2
    intro h
    by_contra h'
    push_neg at h'
    -- take x = 0: cos=1, sin=0
    have h1 := h 0
    -- take x = Real.pi: cos=-1, sin=0
    have h2 := h (Real.pi)
    have h1' : a + a^2 ≥ 2 := by
      have h11 : (sin 0)^2 + a * cos 0 + a^2 ≥ 1 + cos 0 := by
        simpa using h1
      norm_num at h11 ⊢
      nlinarith
    -- h2' is proved through a different route
    have h3 : a^2 - a ≥ 0 := by
      simp [sin_pi, cos_pi] at h2 ⊢
      nlinarith
    nlinarith [sq_nonneg (a -1), sq_nonneg (a + 2)]
  · -- Assume a ≥1 or a ≤ -2, show inequality
    rintro (ha | ha)
    · -- Assume a ≥1
      intro x
      have h1 : cos x ≤ 1 := cos_le_one x
      have h2 : -1 ≤ cos x := neg_one_le_cos x
      have h3 : (sin x) ^ 2 = 1 - (cos x) ^ 2 := by
        have h : (sin x) ^ 2 + (cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        linarith
      rw [h3]
      nlinarith [sq_nonneg (cos x -1), sq_nonneg (cos x +2), sq_nonneg (a -1), sq_nonneg (a +2), sq_nonneg (cos x - a), Real.sin_sq_add_cos_sq x]
    · -- Assume a ≤ -2
      intro x
      have h1 : cos x ≤ 1 := cos_le_one x
      have h2 : -1 ≤ cos x := neg_one_le_cos x
      have h3 : (sin x) ^ 2 = 1 - (cos x) ^ 2 := by
        have h : (sin x) ^ 2 + (cos x) ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        linarith
      rw [h3]
      nlinarith [sq_nonneg (cos x -1), sq_nonneg (cos x +2), sq_nonneg (a -1), sq_nonneg (a +2), sq_nonneg (cos x - a), Real.sin_sq_add_cos_sq x]