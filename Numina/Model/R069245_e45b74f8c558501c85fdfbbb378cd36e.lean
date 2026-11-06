import Mathlib

theorem number_theory_101599 (n : ℕ) :
    (Nat.Prime (2 * n - 1)) →
    (∀ a : Finset ℕ,
      a.card = n →
      (∀ x ∈ a, x > 0) →
      ∃ i ∈ a, ∃ j ∈ a, i ≠ j ∧ (i + j) / Nat.gcd i j ≥ 2 * n - 1) ∧
    (¬Nat.Prime (2 * n - 1)) →
    ∃ a : Finset ℕ,
      a.card = n ∧
      (∀ x ∈ a, x > 0) ∧
      (∀ i ∈ a, ∀ j ∈ a, i ≠ j → (i + j) / Nat.gcd i j < 2 * n - 1) := by
  intro h1 h2
  rcases h2 with ⟨h3, h4⟩
  contradiction