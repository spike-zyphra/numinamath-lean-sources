import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_15607 {g : ℝ → ℝ} (hg : g = λ x => (3 * x + 1) / (x + 8)) :
    {x | x ≠ -8} = {x | x < -8 ∨ x > -8} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume x ≠ -8, prove x < -8 ∨ x > -8
    intro h
    by_cases h1 : x < -8
    · left
      exact h1
    · -- ¬(x < -8)
      have h2 : x ≥ -8 := by linarith
      have h3 : x > -8 := by
        by_contra h4
        push_neg at h4
        have h4 : x ≤ -8 := by linarith
        have h5 : x = -8 := by linarith
        contradiction
      right
      exact h3
  · -- Assume x < -8 ∨ x > -8, prove x ≠ -8
    rintro (h | h)
    · -- Case x < -8
      intro h1
      linarith
    · -- Case x > -8
      intro h1
      linarith