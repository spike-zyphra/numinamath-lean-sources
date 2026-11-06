import Mathlib

theorem number_theory_36092 (n : ℕ) (hn : 2 ≤ n) :
    ∃ p, Nat.Prime p ∧ p > n := by
  have h2 : ∃ p, p ≥ n + 1 ∧ Nat.Prime p := by 
    apply Nat.exists_infinite_primes
    all_goals omega
  rcases h2 with ⟨p, hp1, hp2⟩
  refine ⟨p, hp2, by omega⟩