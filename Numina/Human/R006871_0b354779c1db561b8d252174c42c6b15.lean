import Mathlib

/-
Let $k$ be a natural number greater than 1. Show that there are infinitely many primes $p$ such that $p \equiv 1 \pmod k$.
-/

theorem number_theory (k:ℕ) (hk: 1 < k):
{p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]}.Infinite := by
  
  apply Nat.infinite_setOf_prime_modEq_one
  omega