import Mathlib

theorem algebra_179716 :
    IsLeast {n : ℕ | ∃ x : ℕ, 17 * x + n = 6 * x + 185} 9 ∧
    ∃ n : ℕ, n = 9 ∧ ∃ x : ℕ, 17 * x + n = 6 * x + 185 := by

  constructor
  · constructor
    · -- Show 9 is in the set
      use 16
      all_goals omega
    · -- Show 9 is the smallest
      intro n hn
      rcases hn with ⟨x, hx⟩
      by_contra h
      push_neg at h
      omega
  · -- Show there exists n = 9 with a solution x
    use 9
    constructor
    · rfl
    · use 16
      all_goals omega