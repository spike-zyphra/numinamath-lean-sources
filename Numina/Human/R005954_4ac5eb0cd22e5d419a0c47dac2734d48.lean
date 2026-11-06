import Mathlib

open Complex

/-Find the largest prime factor of $-x^{10}-x^{8}-x^{6}-x^{4}-x^{2}-1$, where $x=2 i$, $i=\sqrt{-1}$.-/
theorem algebra_610907 : let x := 2 * I ; ∃ k : ℕ, - x ^ 10 - x ^ 8 - x ^ 6 - x ^ 4 - x ^ 2 - 1 = k ∧
IsGreatest {p | p ∈ k.primeFactors} 13 := by
-- Simplify the expression in question to $819$
  intro x; dsimp [x]; simp [mul_pow]; norm_num
  rw [show I^10 =(I^2)^5 by rw [← pow_mul]]
  rw [show I^8 =(I^2)^4 by rw [← pow_mul]]
  rw [show I^6 =(I^2)^3 by rw [← pow_mul]]; norm_num
-- Show the prime factors of $819$ is $3$, $7$ and $13$
  use 819; simp; have : Nat.primeFactors 819 = {3, 7, 13} := by
    rw [show 819 = 3^2*7*13 by simp]; repeat rw [Nat.primeFactors_mul]
    rw [Nat.primeFactors_pow]; repeat rw [Nat.Prime.primeFactors]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.union_assoc]
    all_goals norm_num
-- The largest prime factor of $819$ is $13$
  simp [this, IsGreatest]