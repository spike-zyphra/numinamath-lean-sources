import Mathlib

theorem number_theory_262639 (m : ℕ) :
    ∃ n : ℕ, 0 < n ∧ (n ^ 2).divisors.card / m.divisors.card = m ↔
    m = 1 ∨ m = 2 := by
  by_cases h1 : m > 2
  · -- Case m > 2
    use 0
    constructor
    · -- Assume (0 < 0 ∧ (0 ^ 2).divisors.card / m.divisors.card = m), prove m = 1 ∨ m = 2
      intro h
      exfalso
      have h2 : 0 < (0 : ℕ) := by
        tauto
      all_goals omega
    · -- Assume m = 1 ∨ m = 2, prove (0 < 0 ∧ (0 ^ 2).divisors.card / m.divisors.card = m)
      intro h
      exfalso
      have h3 : m > 2 := h1
      omega
  · -- m ≤ 2
    have h2 : m = 0 ∨ m = 1 ∨ m = 2 := by
      omega
    rcases h2 with (h2 | h2 | h2)
    · -- m = 0
      rw [h2]
      use 0
      all_goals simp
    · -- m = 1
      rw [h2]
      use 1
      all_goals native_decide
    · -- m = 2
      rw [h2]
      use 4
      all_goals native_decide