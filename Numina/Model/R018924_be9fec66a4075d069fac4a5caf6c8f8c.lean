import Mathlib

theorem algebra_94742 : ¬(∀ a b : ℝ, a = 0 → a * b = 0) ↔
    ∃ a b : ℝ, a = 0 ∧ b * a ≠ 0 := by
  apply Iff.intro
  · -- Assume the negation of the original, prove the existence
    intro h
    push_neg at h
    simpa using h
  · -- Assume the existence, prove the negation
    intro h
    have h1 : ¬(∀ a b : ℝ, a = 0 → a * b = 0) := by
      intro h2
      rcases h with ⟨a, b, h_eq, h_ne⟩
      have h3 : a * b = 0 := by
        specialize h2 a b h_eq
        simpa using h2
      have h5 : b * a = 0 := by
        have h6 : b * a = a * b := by ring
        rw [h6]
        all_goals
          linarith [h3]
      contradiction
    exact h1