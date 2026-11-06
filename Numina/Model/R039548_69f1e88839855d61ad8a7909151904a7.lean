import Mathlib

theorem number_theory_101993 {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card = ∏ p in n.primeFactors, (n.factorization p + 1) := by
  rw [Nat.card_divisors]
  all_goals simpa using hn