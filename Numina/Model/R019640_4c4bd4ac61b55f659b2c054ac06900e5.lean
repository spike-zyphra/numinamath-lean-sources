import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_180124 (x : ℝ) :
  8.13 * (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0 ↔
  x < 0.75 ∨ x > 4 ∧ x < 7 := by
  constructor
  · -- Assume 8.13 * (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0, prove x < 0.75 ∨ x > 4 ∧ x < 7
    intro h
    by_cases h1 : 4 * x ^ 2 - 19 * x + 12 > 0
    · -- If 4 * x^2 - 19 * x + 12 > 0, then sqrt is positive
      have h2 : sqrt (4 * x ^ 2 - 19 * x + 12) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h3 : 8.13 * (x - 7) < 0 := by
        have h4 : 8.13 * (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0 := h
        have h5 : sqrt (4 * x ^ 2 - 19 * x + 12) > 0 := h2
        apply div_neg_iff.mp at h4
        cases h4 with
        | inl h5 =>
          nlinarith
        | inr h5 =>
          nlinarith
      have h4 : x < 7 := by
        norm_num at h3 ⊢
        nlinarith
      by_cases h5 : x < 0.75
      · -- If x < 0.75, then it's in the first interval
        left
        exact h5
      · -- Assume not h5, so x >= 0.75. Then x must be in (4, 7) because 4x^2 -19x +12 >0
        have h5' : x >= 0.75 := by linarith
        have h6 : x > 4 := by
          by_contra h7
          push_neg at h7
          nlinarith [sq_nonneg (x - 0.75), sq_nonneg (x - 4)]
        have h7 : x < 7 := h4
        right
        constructor <;> linarith
    · -- Assume 4 * x ^ 2 - 19 * x + 12 ≤ 0. Then sqrt is zero or not defined.
      have h2 : sqrt (4 * x ^ 2 - 19 * x + 12) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      rw [h2] at h
      norm_num at h
  · -- Assume x < 0.75 ∨ x > 4 ∧ x < 7, prove 8.13 * (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0
    intro h
    rcases h with h1 | h2
    · -- Assume x < 0.75
      have h3 : 4 * x ^ 2 - 19 * x + 12 > 0 := by
        nlinarith [sq_nonneg (x - 0.75), sq_nonneg (x - 4)]
      have h4 : sqrt (4 * x ^ 2 - 19 * x + 12) > 0 := by
        apply Real.sqrt_pos.mpr
        nlinarith
      have h5 : 8.13 * (x - 7) < 0 := by
        nlinarith
      have h8 : 8.13 * (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0 := by
        apply div_neg_of_neg_of_pos
        all_goals linarith
      exact h8
    · -- Assume x > 4 ∧ x < 7
      rcases h2 with ⟨h3, h4⟩
      have h5 : 4 * x ^ 2 - 19 * x + 12 > 0 := by
        nlinarith [sq_nonneg (x - 0.75), sq_nonneg (x - 4)]
      have h6 : sqrt (4 * x ^ 2 - 19 * x + 12) > 0 := by
        apply Real.sqrt_pos.mpr
        nlinarith
      have h7 : 8.13 * (x - 7) < 0 := by
        nlinarith
      have h8 : 8.13 * (x - 7) / sqrt (4 * x ^ 2 - 19 * x + 12) < 0 := by
        apply div_neg_of_neg_of_pos
        all_goals linarith
      exact h8