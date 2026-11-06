import Mathlib

theorem number_theory_68444 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmn : n ≥ m ∧ m ≥ 1) :
    ∃ k, k = Nat.gcd m n * Nat.choose n m / n := by
  refine' ⟨Nat.gcd m n * Nat.choose n m / n, rfl⟩