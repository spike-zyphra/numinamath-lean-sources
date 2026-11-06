import Mathlib

theorem number_theory_8059 (m n : ℕ) (hmn : m ≥ n ∧ n ≥ 1) :
    ∃ k, (Nat.gcd m n) * Nat.choose m n / m = k := by 
  refine' ⟨(Nat.gcd m n) * Nat.choose m n / m, rfl⟩