import Mathlib

/- Let $n = 2^4 \cdot 3^5 \cdot 4^6\cdot 6^7$. How many natural-number factors does $n$ have?-/
theorem number_theory_11618 {n : ℕ} (hn : n = 2^4 * 3^5 * 4^6 * 6^7) :
    n.divisors.card = 312 := by
  -- After simple calculation, we have 2^4 * 3^5 * 4^6 * 6^7 = 2^23 * 3^12.
  rw [show n = 2 ^ 23 * 3 ^ 12 by norm_num [hn]]
  set p := 2
  set q := 3
  set a := 23
  set b := 12
  -- p=2 is prime.
  have hpp : p.Prime := by norm_num
  -- q=3 is prime.
  have hqp : q.Prime := by norm_num
  -- Notice that p,q are prime, we have the number of divisors of $p^aq^b=(a+1)(b+1)$.
  rw [← ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.IsMultiplicative.map_mul_of_coprime,
    ArithmeticFunction.sigma_zero_apply_prime_pow, ArithmeticFunction.sigma_zero_apply_prime_pow]
  norm_num
  . exact hqp
  . exact hpp
  -- $\sigma(n)$ is multiplicative
  . arith_mult
  apply Nat.coprime_pow_primes
  all_goals norm_num
