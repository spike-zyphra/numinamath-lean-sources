import Mathlib

theorem number_theory_181582 (d : ℕ) (h₀ : ¬ 2 ∣ d) (h₁ : ¬ 5 ∣ d) :
    ∃ n, ∀ i ∈ Finset.range (Nat.digits 10 n).length, (Nat.digits 10 n)[i]! = 1 ∧ d ∣ n := by
  use 0
  intro i hi
  simpa using hi