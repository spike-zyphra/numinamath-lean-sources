import Mathlib

theorem number_theory_6860 (n : ℕ) (h : n % 11 = 3 ∧ n % 12 = 2 ∧ n % 13 = 1) :
    ∃ k, n = 14 + 1716 * k := by
  rcases h with ⟨h₁, h₂, h₃⟩
  use (n / 1716)
  omega