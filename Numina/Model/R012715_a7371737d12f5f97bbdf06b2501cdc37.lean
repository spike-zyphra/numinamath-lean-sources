import Mathlib

theorem number_theory_218661 (m n : ℕ) :
    ∃ p : ℕ, p.Prime ∧ 9^m + 3^m - 2 = 2 * p^n ↔ (m = 1 ∧ n = 1) := by
  by_cases h : m = 1 ∧ n = 1
  · -- m = 1 and n = 1
    rcases h with ⟨rfl, rfl⟩
    use 5
    all_goals
      norm_num
  · -- m ≠ 1 or n ≠ 1
    use 0
    constructor
    · -- Assume p = 0 is prime and 9^m + 3^m - 2 = 2 * 0^n, prove m = 1 ∧ n = 1
      intro h2
      rcases h2 with ⟨h3, h4⟩
      norm_num at h3
    · -- Assume m = 1 ∧ n = 1, prove p = 0 is prime and 9^m + 3^m - 2 = 2 * 0^n
      intro h2
      exfalso
      apply h
      tauto