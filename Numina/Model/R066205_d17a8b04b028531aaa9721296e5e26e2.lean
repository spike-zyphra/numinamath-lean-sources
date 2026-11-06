import Mathlib

theorem number_theory_122860 (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by 
  apply Nat.card_divisors (by assumption)