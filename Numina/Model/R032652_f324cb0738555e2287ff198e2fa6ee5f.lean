import Mathlib

theorem number_theory_104027 (n : ℕ) :
    ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ y^2 + x * y + 3 * x = n * (x^2 + x * y + 3 * y) ↔
    n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 9 := by
  by_cases h1 : n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 9
  · -- n is in {1, 3, 4, 9}.
    rcases h1 with (rfl | rfl | rfl | rfl)
    · -- n = 1.
      use 1, 1
      all_goals simp
    · -- n = 3.
      use 1, 11
      all_goals norm_num
    · -- n = 4.
      use 4, 26
      all_goals norm_num
    · -- n = 9.
      use 5, 70
      all_goals norm_num
  · -- n is not in {1, 3, 4, 9}.
    have h2 : ¬ (n = 1 ∨ n = 3 ∨ n = 4 ∨ n = 9) := by
      intro h
      tauto
    use 0, 0
    simp at *
    all_goals
      try { tauto }