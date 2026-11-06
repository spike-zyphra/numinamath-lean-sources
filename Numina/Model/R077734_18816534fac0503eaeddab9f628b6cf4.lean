import Mathlib

theorem number_theory_113927 {n : ℕ} (hn : n ≥ 2) :
    n.divisors.card = ∏ p in n.primeFactors, (n.factorization p + 1) := by
  apply Nat.card_divisors (by linarith)