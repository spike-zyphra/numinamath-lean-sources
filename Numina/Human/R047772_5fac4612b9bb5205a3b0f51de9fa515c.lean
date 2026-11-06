import Mathlib
/- Compute the prime factorization of 1007021035035021007001 . (You should write your answer in the form $p_{1}^{e_{1}} p_{2}^{e_{2}} \ldots p_{k}^{e_{k}}$, where $p_{1}, \ldots, p_{k}$ are distinct prime numbers and $e_{1}, \ldots, e_{k}$ are positive integers.) -/
theorem number_theory_609108 : 1007021035035021007001 = 7 ^ 7 * 11 ^ 7 * 13 ^ 7 ∧ Nat.Prime 7 ∧ Nat.Prime 11 ∧ Nat.Prime 13 ∧ 7 ≠ 11 ∧ 7 ≠ 13 ∧ 11 ≠ 13:= by
  -- use norm_num to check the factorization and calculate the prime factors
  norm_num
