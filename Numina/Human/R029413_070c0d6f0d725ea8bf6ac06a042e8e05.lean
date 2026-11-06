import Mathlib

open Finset Nat

/- For n a positive integer, let f(n) be the quotient obtained when the sum of all positive divisors of n is divided by n. For example,
f(14)=(1+2+7+14)÷14=12/7

What is f(768)−f(384)?

(A) 1/768(B) 1/192(C) 1(D) 4/3(E) 8/3 -/
theorem number_theory_94854 {f : ℕ → ℝ}
(hf : ∀ n, f n = (∑ d ∈ (n.divisors), d) / n) :
f 768 - f 384 = 1 / 192 := by
  -- Have factorization, and prime factorization all ready
  have factor_768 : 768 = 2^8 * 3 := by norm_num
  have factor_384 : 384 = 2^7 * 3 := by norm_num
  have primes_768 : primeFactors 768 = {2, 3} := by
    rw [factor_768]
    repeat rw [primeFactors_mul (by linarith) (by linarith)]
    · rw [primeFactors_pow_succ]
      repeat rw [Prime.primeFactors (by norm_num)]
      rfl
  have primes_384 : primeFactors 384 = {2, 3} := by
    rw [factor_384]
    repeat rw [primeFactors_mul (by linarith) (by linarith)]
    · rw [primeFactors_pow_succ]
      repeat rw [Prime.primeFactors (by norm_num)]
      rfl
  have factorization_768 : (768).factorization 2 = 8 ∧ (768).factorization 3 = 1 := by
    rw [factor_768]
    repeat rw [Nat.factorization_mul (by linarith) (by linarith)]
    norm_num
    constructor
    · have : 256 = 2^8 := by norm_num
      rw [this, factorization_pow, Prime.factorization]
      simp; norm_num
    repeat rw [factorization_eq_zero_of_not_dvd (by norm_num)]
  have factorization_384 : (384).factorization 2 = 7 ∧ (384).factorization 3 = 1 := by
    rw [factor_384]
    repeat rw [Nat.factorization_mul (by linarith) (by linarith)]
    norm_num
    constructor
    · have : 128 = 2^7 := by norm_num
      rw [this, factorization_pow, Prime.factorization]
      simp; norm_num
    repeat rw [factorization_eq_zero_of_not_dvd (by norm_num)]

  -- Calculate f(768) through prime factorization
  have f768 : f 768 = 2044 / 768 := by
    rw [hf 768, sum_divisors]
    field_simp
    simp [primes_768, factorization_768]
    norm_num
    positivity

  -- Calculate f(384) through prime factorization
  have f384 : f 384 = 1020 / 384 := by
    rw [hf 384, sum_divisors]
    field_simp
    simp [primes_384, factorization_384]
    norm_num
    positivity
  rw [f768, f384]
  norm_num