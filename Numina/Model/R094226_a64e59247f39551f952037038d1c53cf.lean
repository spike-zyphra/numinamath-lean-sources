import Mathlib

open Real Set
open scoped Real

theorem inequalities_240523 (a : ℝ) :
  (∀ x : ℝ, sin x ^ 2 + a * cos x + a ^ 2 ≥ 1 + cos x) ↔ a ≥ 1 ∨ a ≤ -2 := by
  constructor
  · -- Assume the inequality holds for all x, prove a ≥ 1 ∨ a ≤ -2
    intro h
    have h0 := h 0
    have h1 := h (Real.pi)
    have h0' : sin (0 : ℝ) = 0 := sin_zero
    have h0'' : cos (0 : ℝ) = 1 := cos_zero
    have h1' : sin (Real.pi : ℝ) = 0 := sin_pi
    have h1'' : cos (Real.pi : ℝ) = -1 := cos_pi
    rw [h0', h0''] at h0
    rw [h1', h1''] at h1
    have h2 : a ^ 2 + a - 2 ≥ 0 := by nlinarith
    have h3 : a ^ 2 - a ≥ 0 := by nlinarith
    by_cases h4 : a ≥ 1
    · -- if a ≥ 1, then we are done
      left
      exact h4
    · -- if not a ≥ 1, then a < 1
      have h4' : a < 1 := by linarith
      have h5 : a ≤ 0 := by nlinarith
      have h6 : a ≤ -2 := by nlinarith
      right
      linarith
  · -- Assume a ≥ 1 ∨ a ≤ -2, prove ∀ x : ℝ, sin x ^ 2 + a * cos x + a ^ 2 ≥ 1 + cos x
    rintro (h | h)
    · -- if a ≥ 1
      intro x
      have h1 : -1 ≤ cos x ∧ cos x ≤ 1 := by
        constructor
        · exact neg_one_le_cos x
        · exact cos_le_one x
      nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (a - 1), sq_nonneg (a + 2), Real.cos_sq_add_sin_sq x]
    · -- if a ≤ -2
      intro x
      have h1 : -1 ≤ cos x ∧ cos x ≤ 1 := by
        constructor
        · exact neg_one_le_cos x
        · exact cos_le_one x
      nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1), sq_nonneg (a - 1), sq_nonneg (a + 2), Real.cos_sq_add_sin_sq x]