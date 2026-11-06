import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_18584 {f : ℝ → ℝ}
  (hf : f = λ x => (2 * x - 3) * (2 * x + 5) / ((3 * x - 9) * (3 * x + 6))) :
  {x | x ≠ -2 ∧ x ≠ 3} = {x | x < -2 ∨ x ∈ Ioo (-2) 3 ∨ x > 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- Assume x ≠ -2 ∧ x ≠ 3, prove x < -2 ∨ (x > -2 ∧ x < 3) ∨ x > 3
    rintro ⟨h₁, h₂⟩
    by_cases h3 : x < -2
    · -- Case x < -2
      left
      exact h3
    · -- Case x ≥ -2
      have h4 : x > -2 := by
        by_contra h
        push_neg at h
        have : x = -2 := by linarith
        contradiction
      by_cases h5 : x < 3
      · -- Case -2 < x < 3
        right
        left
        constructor
        · -- Show x > -2
          linarith
        · -- Show x < 3
          exact h5
      · -- Case x ≥ 3
        have h6 : x > 3 := by
          by_contra h
          push_neg at h
          have : x = 3 := by linarith
          contradiction
        right
        right
        exact h6
  · -- Assume x < -2 ∨ (x > -2 ∧ x < 3) ∨ x > 3, prove x ≠ -2 ∧ x ≠ 3
    rintro (h | ⟨h₁, h₂⟩ | h)
    · -- Case x < -2
      constructor
      · -- Show x ≠ -2
        by_contra h'
        have : x = -2 := by linarith
        linarith
      · -- Show x ≠ 3
        by_contra h'
        have : x = 3 := by linarith
        linarith
    · -- Case -2 < x < 3
      constructor
      · -- Show x ≠ -2
        by_contra h'
        have : x = -2 := by linarith
        linarith
      · -- Show x ≠ 3
        by_contra h'
        have : x = 3 := by linarith
        linarith
    · -- Case x > 3
      constructor
      · -- Show x ≠ -2
        by_contra h'
        have : x = -2 := by linarith
        linarith
      · -- Show x ≠ 3
        by_contra h'
        have : x = 3 := by linarith
        linarith