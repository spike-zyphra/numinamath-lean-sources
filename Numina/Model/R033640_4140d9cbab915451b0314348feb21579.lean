import Mathlib

theorem number_theory_137238 (n : ℕ) :
    ∃ a b, a > 0 ∧ b > 0 ∧ n = 2 * (a + b) ∧ n = a * b ↔ n = 16 ∨ n = 18 := by
  by_cases h : n = 16 ∨ n = 18
  · -- Case where n = 16 ∨ n = 18
    rcases h with (h | h)
    · -- n = 16
      have hn : n = 16 := h
      use 4, 4
      simp [hn]
      <;> omega
    · -- n = 18
      have hn : n = 18 := h
      use 3, 6
      simp [hn]
      <;> omega
  · -- Case where n ≠ 16 and n ≠ 18
    push_neg at h
    use 0, 0
    simp at h ⊢
    all_goals
      try tauto