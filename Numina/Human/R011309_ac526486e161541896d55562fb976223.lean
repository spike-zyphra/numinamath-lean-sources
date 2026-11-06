import Mathlib

/-The number $27,000,001$ has exactly four prime factors. Find their sum.-/
theorem number_theory_611311 : (Nat.primeFactors 27000001).card = 4 ∧
(Nat.primeFactors 27000001).sum id = 652 := by
-- Prove a factorization formula for $27*x^6+1$
  have : ∀ x > 0, 27 * x ^ 6 + 1 = (3 * x ^ 2 + 1) * (3 * x ^ 2 + 3 * x + 1) * (3 * x ^ 2 - 3 * x + 1) := by
    intro x hx; zify; rw [Nat.cast_sub]; push_cast; ring
    rw [pow_two, ← mul_assoc]; apply Nat.le_mul_of_pos_right; exact hx
-- Plug in $x=10$ to this formula
  specialize this 10 (by norm_num1); rw [show 27 * 10 ^ 6 + 1 = 27000001 by norm_num1] at this
-- Use Nat.primeFactors_mul to simplify, the goal follows
  rw [this, Nat.primeFactors_mul, Nat.primeFactors_mul]; norm_num1
  rw [show 301 = 7 * 43 by norm_num, Nat.primeFactors_mul]
  repeat rw [Nat.Prime.primeFactors]
  simp [Finset.sum_union]
  all_goals norm_num1
