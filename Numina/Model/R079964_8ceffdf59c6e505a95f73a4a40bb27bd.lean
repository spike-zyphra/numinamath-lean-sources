import Mathlib

theorem algebra_288356 (x : ℝ) : x + abs x = 0 ↔ x ≤ 0 := by
  constructor
  · -- Forward implication: if x + |x| = 0, then x ≤ 0
    intro h
    by_cases h1 : x ≥ 0
    · -- If x ≥ 0, then |x| = x
      rw [abs_of_nonneg h1] at h
      have h2 : x = 0 := by linarith
      linarith
    · -- Case x < 0
      have h2 : x < 0 := by linarith
      rw [abs_of_neg h2] at h
      linarith
  · -- Backward implication: if x ≤ 0, then x + |x| = 0
    intro h
    have h1 : abs x = -x := by
      rw [abs_of_nonpos h]
    rw [h1]
    linarith