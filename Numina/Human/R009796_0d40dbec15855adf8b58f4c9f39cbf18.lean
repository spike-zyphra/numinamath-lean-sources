import Mathlib

/- 11. [6] Compute the prime factorization of 1007021035035021007001 . (You should write your answer in the form $p_{1}^{e_{1}} p_{2}^{e_{2}} \ldots p_{k}^{e_{k}}$, where $p_{1}, \ldots, p_{k}$ are distinct prime numbers and $e_{1}, \ldots, e_{k}$ are positive integers.) -/
theorem number_theory_162314 : (Nat.primeFactors (1007021035035021007001)) = {7, 11, 13} ∧
    (Nat.primeFactors (1007021035035021007001)).card = 3 ∧
    (Nat.factorization (1007021035035021007001) 7) = 7 ∧
    (Nat.factorization (1007021035035021007001) 11) = 7 ∧
    (Nat.factorization (1007021035035021007001) 13) = 7 := by
  -- the value is 7^7 * 11^7 * 13^7
  -- prove 7,11,13 as primes
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h13 : Nat.Prime 13 := by norm_num
  -- prove the number's prime factors are 7,11,13 by breaking it to coprime factors
  have h : Nat.primeFactors (1007021035035021007001) = {7, 11, 13} := by
    convert_to Nat.primeFactors (7^7) ∪ Nat.primeFactors (11^7) ∪ Nat.primeFactors (13^7) = {7, 11, 13}
    . rw [← Nat.Coprime.primeFactors_mul (by norm_num), ← Nat.Coprime.primeFactors_mul (by norm_num)]
      norm_num
    rw [Nat.primeFactors_prime_pow (by norm_num) h7, Nat.primeFactors_prime_pow (by norm_num) h11, Nat.primeFactors_prime_pow (by norm_num) h13]
    ext x ; simp
  -- now prove the goals
  and_intros
  . exact h
  . rw [h]
    simp
  -- prove the factorization values by again breaking to coprime parts
  . convert_to Nat.factorization (7^7) 7 = 7
    . nth_rw 2 [← Nat.factorization_eq_of_coprime_left (b := 11^7 * 13^7)]
      simp; norm_num; simp [h7]; norm_num
    rw [Nat.Prime.factorization_pow h7]
    simp
  . convert_to Nat.factorization (11^7) 11 = 7
    . nth_rw 2 [← Nat.factorization_eq_of_coprime_left (b := 7^7 * 13^7)]
      simp; norm_num; simp [h11]; norm_num
    rw [Nat.Prime.factorization_pow h11]
    simp
  . convert_to Nat.factorization (13^7) 13 = 7
    . nth_rw 2 [← Nat.factorization_eq_of_coprime_left (b := 7^7 * 11^7)]
      simp; norm_num; simp [h13]; norm_num
    rw [Nat.Prime.factorization_pow h13]
    simp