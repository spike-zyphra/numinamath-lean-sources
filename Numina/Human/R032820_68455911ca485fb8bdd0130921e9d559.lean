import Mathlib

open Nat Set

/- For each positive integer k, let Sk denote the increasing arithmetic sequence of integers whose first term is 1 and whose common difference is k.
   For example, S3 is the sequence 1,4,7,10,…. For how many values of k does Sk contain the term 2005? -/
theorem number_theory_98579 :
Set.ncard {k | 0 < k ∧ ∃ n, 1 + k * n = 2005} = 12 := by
  -- Prove that k works if and only if k is a divisor of 2004
  have divisor_solves : ∀ k, (∃ n, 1 + k * n = 2005) ↔ k ∈ divisors 2004 := by
    intro k
    constructor
    · rintro ⟨n, hn⟩
      simp [add_comm] at hn
      simp
      exact dvd_of_mul_right_eq n hn
    intro hk
    apply dvd_of_mem_divisors at hk
    rcases exists_eq_mul_left_of_dvd hk with ⟨n, hn⟩
    use n
    linarith [hn]

  -- Characterize the set of all k to be divisors of 2004
  have : {k | 0 < k ∧ ∃ n, 1 + k * n = 2005} = divisors 2004 := by
    ext k
    dsimp
    constructor
    · rintro ⟨k_pos, hk⟩
      exact (divisor_solves k).1 hk
    intro hk
    constructor
    · exact pos_of_mem_divisors hk
    exact (divisor_solves k).2 hk

  -- Rewrite the goal to be equivalent to finding number of divisors of 2004
  rw [this]
  simp
  rw [card_divisors (by linarith)]

  -- Factorization of 2004, useful in multiple proofs
  have factor_2004 : 2004 = 2^2 * 3 * 167 := by norm_num

  -- Count the number of divisors of 2004
  have primes_2004 : primeFactors 2004 = {2, 3, 167} := by
    rw [factor_2004]
    repeat rw [primeFactors_mul (by linarith) (by linarith)]
    · rw [primeFactors_pow_succ]
      repeat rw [Prime.primeFactors (by norm_num)]
      rfl
  rw [primes_2004]

  -- Completely determine factorization of 2004
  have factorization_2004 : (2004).factorization 2 = 2 ∧ (2004).factorization 3 = 1 ∧ (2004).factorization 167 = 1 := by
    rw [factor_2004]
    repeat rw [Nat.factorization_mul (by linarith) (by linarith)]
    norm_num
    constructor
    · have : 4 = 2^2 := by norm_num
      rw [this, factorization_pow, Prime.factorization]
      simp; norm_num
    constructor
    repeat rw [factorization_eq_zero_of_not_dvd (by norm_num)]
  simp [factorization_2004]