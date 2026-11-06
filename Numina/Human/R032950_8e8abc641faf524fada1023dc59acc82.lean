import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_175117 (a : ℝ) :
  (∀ x : ℝ, |x - a| + |x - 12| ≥ 6) ↔ a ≤ 6 ∨ a ≥ 18 := by
  constructor
  · -- Assume |x - a| + |x - 12| ≥ 6 holds for all x
    intro h
    by_contra! h_contra
    specialize h 12
    rw [sub_self, abs_zero, add_zero] at h
    by_cases ha : a ≤ 12
    . rw [abs_of_nonneg (by linarith)] at h
      linarith only [h_contra, h]
    . rw [abs_of_neg (by linarith)] at h
      linarith only [h_contra, h]
  · -- Assume a ≤ 6 ∨ a ≥ 18, prove |x - a| + |x - 12| ≥ 6
    rintro (h | h) x
    · -- Case a ≤ 6
      by_cases h1 : x ≥ 12
      · -- If x ≥ 12, then |x - 12| = x - 12
        rw [abs_of_nonneg (by linarith)]
        by_cases h2 : x ≥ a
        · -- If x ≥ a, then |x - a| = x - a
          rw [abs_of_nonneg (by linarith)]
          linarith
        · -- If x < a, then |x - a| = a - x
          rw [abs_of_nonpos (by linarith)]
          linarith
      · -- If x < 12, then |x - 12| = 12 - x
        rw [abs_of_nonpos (show x - 12 ≤ 0 by linarith)]
        by_cases h2 : x ≥ a
        · -- If x ≥ a, then |x - a| = x - a
          rw [abs_of_nonneg (by linarith)]
          linarith
        · -- If x < a, then |x - a| = a - x
          rw [abs_of_nonpos (by linarith)]
          linarith
    · -- Case a ≥ 18
      by_cases h1 : x ≥ 12
      · -- If x ≥ 12, then |x - 12| = x - 12
        rw [abs_of_nonneg (show 0 ≤ x - 12 by linarith)]
        by_cases h2 : x ≥ a
        · -- If x ≥ a, then |x - a| = x - a
          rw [abs_of_nonneg (by linarith)]
          linarith
        · -- If x < a, then |x - a| = a - x
          rw [abs_of_nonpos (by linarith)]
          linarith
      · -- If x < 12, then |x - 12| = 12 - x
        rw [abs_of_nonpos (by linarith)]
        by_cases h2 : x ≥ a
        · -- If x ≥ a, then |x - a| = x - a
          rw [abs_of_nonneg (by linarith)]
          linarith
        · -- If x < a, then |x - a| = a - x
          rw [abs_of_nonpos (by linarith)]
          linarith
