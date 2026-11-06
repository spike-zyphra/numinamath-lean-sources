import Mathlib

theorem number_theory_275341 (n m : ℕ) (hnm : n ≥ m ∧ m ≥ 1) :
    ∃ k, k = Nat.gcd m n * Nat.choose n m / n := by
  refine' ⟨Nat.gcd m n * Nat.choose n m / n, rfl⟩