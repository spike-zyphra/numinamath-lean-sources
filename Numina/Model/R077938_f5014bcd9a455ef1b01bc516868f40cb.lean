import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_326234 (a : ℝ) :
  (∀ x : ℝ, sin x ^ 2 + a * cos x + a ^ 2 ≥ 1 + cos x) ↔ a ≥ 1 ∨ a ≤ -2 := by
  constructor
  · -- Assume the inequality holds for all x, we need to prove a ≥ 1 or a ≤ -2
    intro h
    have h1 := h 0
    have h1' : a ^ 2 + a - 2 ≥ 0 := by
      have h1 := h 0
      norm_num at h1 ⊢
      nlinarith
      all_goals linarith
    have h2 := h (Real.pi)
    have h2' : a * (a - 1) ≥ 0 := by
      have h2 := h (Real.pi)
      have hsin : sin (Real.pi) = 0 := by
        exact sin_pi
      have hcos : cos (Real.pi) = -1 := by
        exact cos_pi
      rw [hsin, hcos] at h2
      nlinarith
    have h4 : a ≥ 1 ∨ a ≤ -2 := by
      by_cases ha : a ≥ 1
      · left
        exact ha
      · -- Assume a < 1
        have h5 : a < 1 := by nlinarith
        have h6 : a ≤ 0 := by
          have h7 : a * (a - 1) ≥ 0 := by linarith [h2']
          nlinarith
        have h8 : a ≤ -2 := by
          have h9 : a ^ 2 + a - 2 ≥ 0 := by linarith [h1']
          nlinarith
        right
        linarith
    exact h4
  · -- Assume a ≥ 1 or a ≤ -2, prove the inequality holds for all x
    rintro (ha | ha)
    · -- Case a ≥ 1
      intro x
      have h1 : sin x ^ 2 + a * cos x + a ^ 2 ≥ 1 + cos x := by
        nlinarith [sq_nonneg (sin x), sq_nonneg (cos x - 1), sq_nonneg (cos x + 2),
                  sq_nonneg (a - 1), sq_nonneg (a + 2), sq_nonneg (a - 1 - 2 * cos x),
                  Real.sin_sq_add_cos_sq x, Real.cos_le_one x, Real.neg_one_le_cos x]
      exact h1
    · -- Case a ≤ -2
      intro x
      have h1 : sin x ^ 2 + a * cos x + a ^ 2 ≥ 1 + cos x := by
        nlinarith [sq_nonneg (sin x), sq_nonneg (cos x - 1), sq_nonneg (cos x + 2),
                  sq_nonneg (a - 1), sq_nonneg (a + 2), sq_nonneg (a - 1 - 2 * cos x),
                  Real.sin_sq_add_cos_sq x, Real.cos_le_one x, Real.neg_one_le_cos x]
      exact h1