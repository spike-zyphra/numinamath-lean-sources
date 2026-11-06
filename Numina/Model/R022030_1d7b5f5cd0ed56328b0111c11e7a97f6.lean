import Mathlib


theorem algebra_305248 (n : ℕ) (hn : n > 0) :
    ∃ m, m > 0 ∧ n^2 + 9 * n + 98 = m * (m + 1) ↔ n = 34 ∨ n = 14 ∨ n = 7 := by
  by_cases h : n = 34 ∨ n = 14 ∨ n = 7
  · -- Assume n = 34 ∨ n = 14 ∨ n = 7, prove ∃ m the equivalence.
    rcases h with (r | r | r)
    · -- When n = 34, m = 39.
      use 39
      rw [r]
      constructor
      · norm_num
      · norm_num
    · -- When n = 14, m = 20.
      use 20
      rw [r]
      constructor
      · norm_num
      · norm_num
    · -- When n = 7, m = 14.
      use 14
      rw [r]
      constructor
      · norm_num
      · norm_num
  · -- Assume ¬ (n = 34 ∨ n = 14 ∨ n = 7), prove the equivalence with ∃ m.
    use 0
    simp at *
    all_goals
    try tauto