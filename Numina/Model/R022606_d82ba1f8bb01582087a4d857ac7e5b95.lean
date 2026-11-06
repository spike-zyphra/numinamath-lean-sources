import Mathlib

theorem number_theory_240687 : ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ∃ k : ℤ, n / (Nat.divisors n).card = k := by 
  intro N
  use N + 1
  constructor 
  · -- Show n > N
    omega
  · -- Show ∃ k : ℤ, (N + 1) / (Nat.divisors (N + 1)).card = k
    refine' ⟨(N + 1) / (Nat.divisors (N + 1)).card, by simp⟩