import Mathlib

theorem number_theory_230445 {n : ℕ} :
    n = ∑ d in n.divisors, (Nat.totient d) := by
  rw [Nat.sum_totient]