import Mathlib

theorem number_theory_101667 {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card = ∏ i ∈ n.primeFactors, (n.factorization i + 1) := by 
  apply Nat.card_divisors (by assumption)