import Mathlib

/-A natural number has 10 different divisors (i.e., factors, which are natural numbers that can divide it),
but its prime factors (i.e., factors that are prime numbers) are only 2 and 3. Therefore, this natural number is -/

theorem number_theory_254962: {n: ℕ | (Nat.divisors n).card = 10 ∧ n.primeFactors = {2, 3}} = {48, 162} := by

  ext n
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    rcases h with ⟨h, l⟩
    rw [Nat.card_divisors] at h
    simp [l] at h
    have hn: n ≠ 0 := by
      by_contra! s
      simp [s] at l
      absurd l
      decide

    -- we show that there are only two cases for the power of 2 and 3
    have o: n.factorization 2 = 1 ∧ n.factorization 3 = 4 ∨
             n.factorization 2 = 4 ∧ n.factorization 3 = 1 := by
      set a:= n.factorization 2
      set b:= n.factorization 3
      have la: a ≠ 0 := by
        by_contra! o
        simp [a] at o
        rw [Nat.factorization_eq_zero_iff] at o
        have g: Nat.Prime 2 := by
          norm_num
        simp [hn, g] at o
        have j: 2 ∣ n := by
          apply Nat.dvd_of_mem_primeFactors
          rw [l]
          decide
        omega
      have lb: b ≠ 0 := by
        by_contra! o
        simp [b] at o
        rw [Nat.factorization_eq_zero_iff] at o
        have g: Nat.Prime 3 := by
          norm_num
        simp [hn, g] at o
        have j: 3 ∣ n := by
          apply Nat.dvd_of_mem_primeFactors
          rw [l]
          decide
        omega
      have d1: a + 1 ∈ Nat.divisors 10 := by
        simp
        rw [← h]
        simp
      rw [show Nat.divisors 10 = {1, 2, 5, 10} by native_decide] at d1
      simp at d1
      simp [la] at d1
      rcases d1 with q | q | q
      .
        simp [q] at h
        replace h: b = 4 := by omega
        simp [q, h]
      .
        simp [q] at h
        simp [q, h]
        omega
      .
        simp [q] at h
        simp [h] at lb

    -- then we can compute n by factorization
    have i:= Nat.factorization_prod_pow_eq_self hn
    rw [Nat.prod_factorization_eq_prod_primeFactors] at i
    simp [h, l] at i
    rcases o with o | o
    .
      simp [o] at i
      simp [i]
    .
      simp [o] at i
      simp [i]

    by_contra! o
    simp [o] at h


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
      native_decide
    .
      simp [h]
      native_decide