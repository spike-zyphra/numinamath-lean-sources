import Mathlib

/-The solution set of the inequality $x^2 - x < 0$ is-/
theorem algebra_9194 (x : ℝ) : x^2 - x < 0 ↔ 0 < x ∧ x < 1 := by
  -- Factorization of the quadratic expression
  have quadratic_factorization (x : ℝ) : x^2 - x = x*(x-1) := by
    ring
  rw [quadratic_factorization]
  constructor
  · intro h
    have h_cases : (x < 0 ∧ x-1 > 0) ∨ (x > 0 ∧ x-1 < 0) := by
      apply Or.symm
      exact mul_neg_iff.1 h
    rcases h_cases with ⟨h_left, h_right⟩ | ⟨h_left, h_right⟩
    · -- Case 1: Impossible case
      have : 0 > 1 := by linarith
      have : 0 ≤ 1 := zero_le_one
      linarith
    · -- Case 2: The actual solution
      constructor
      · exact h_left
      · have : x < 1 := by linarith
        exact this
  · intro ⟨h_left, h_right⟩
    have : x-1 < 0 := by linarith
    apply mul_neg_of_pos_of_neg
    · exact h_left
    · exact this
