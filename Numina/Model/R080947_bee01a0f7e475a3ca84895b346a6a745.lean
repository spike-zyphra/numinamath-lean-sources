import Mathlib

theorem number_theory_194396 (n : ℕ) :
    ∃ k, (n + 10) / (n + 2) = k ↔ n = 2 ∨ n = 6 := by
  by_cases h1 : n = 2
  · -- If n = 2, then (2 + 10) / (2 + 2) = 12 / 4 = 3
    use 3
    simp [h1]
  · -- n ≠ 2
    by_cases h2 : n = 6
    · -- If n = 6, then (6 + 10) / (6 + 2) = 16 / 8 = 2
      use 2
      simp [h2]
    · -- n ≠ 2 and n ≠ 6
      use 0
      simp [h1, h2]
      all_goals omega