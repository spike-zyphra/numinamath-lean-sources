import Mathlib

theorem number_theory_6975 (n : ℕ) (h₀ : n ≠ 0) :
    n.divisors.card = ∏ i ∈ n.primeFactors, (n.factorization i + 1) := by
  apply Nat.card_divisors (by assumption)