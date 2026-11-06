import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_175117 (a : ℝ) :
  (∀ x : ℝ, |x - a| + |x - 12| ≥ 6) ↔ a ≤ 6 ∨ a ≥ 18 := by
  constructor
  · -- Assume that ∀ x, |x - a| + |x - 12| ≥ 6, prove a ≤ 6 ∨ a ≥ 18
    intro h
    have h1 := h a
    have h2 : |a - a| + |a - 12| ≥ 6 := by simpa using h1
    have h3 : |a - 12| ≥ 6 := by
      simp at h2 ⊢
      all_goals linarith
    cases' abs_choice (a - 12) with h4 h4
    · -- Case 1: |a - 12| = a - 12
      right
      linarith
    · -- Case 2: |a - 12| = -(a - 12)
      left
      linarith
  · -- Assume a ≤ 6 ∨ a ≥ 18, prove ∀ x, |x - a| + |x - 12| ≥ 6
    rintro (h | h)
    · -- Case 1: a ≤ 6
      intro x
      have h1 : |x - a| + |x - 12| ≥ |(x - a) - (x - 12)| := by
        apply abs_sub
      have h2 : (x - a) - (x - 12) = 12 - a := by ring
      have h3 : |(x - a) - (x - 12)| = |12 - a| := by 
        rw [h2]
      have h4 : |12 - a| ≥ 6 := by
        rw [abs_of_nonneg (by linarith)]
        all_goals linarith
      linarith [abs_nonneg (x - a), abs_nonneg (x - 12), abs_nonneg (12 - a), h1, h3, h4]
    · -- Case 2: a ≥ 18
      intro x
      have h1 : |x - a| + |x - 12| ≥ |(x - a) - (x - 12)| := by 
        apply abs_sub
      have h2 : (x - a) - (x - 12) = 12 - a := by ring
      have h3 : |(x - a) - (x - 12)| = |12 - a| := by 
        rw [h2]
      have h4 : |12 - a| ≥ 6 := by 
        rw [abs_of_nonpos (by linarith)]
        all_goals linarith
      linarith [abs_nonneg (x - a), abs_nonneg (x - 12), abs_nonneg (12 - a), h1, h3, h4]