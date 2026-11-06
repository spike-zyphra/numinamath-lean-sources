import Mathlib

/- Task solved by cyrix

# Task 2 - 261222

Determine all triples $(p, q, r)$ of prime numbers that satisfy the following conditions (1), (2):

(1) In the sequence of all prime numbers, $p, q, r$ are consecutive prime numbers in this order.

(2) The number $s=p^{2}+q^{2}+r^{2}$ is a prime number. -/
theorem number_theory_199190 (p q r s : ℕ) (hsum : s = p^2 + q^2 + r^2)
  : s.Prime ∧ (∃ k, Nat.nth Nat.Prime k = p ∧ Nat.nth Nat.Prime (k+1) = q ∧ Nat.nth Nat.Prime (k+2) = r)
    ↔ (p, q, r) = (3, 5, 7)
  := by

    -- 7 and 11 are prime
    have prime_seven : Nat.Prime 7 := by decide
    have prime_eleven : Nat.Prime 11 := by decide

    -- the first five primes are 2, 3, 5, 7, 11
    have prime_0_eq_2 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
    have prime_1_eq_3 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    have prime_2_eq_5 : Nat.nth Nat.Prime 2 = 5 := Nat.nth_count Nat.prime_five
    have prime_3_eq_7 : Nat.nth Nat.Prime 3 = 7 := Nat.nth_count prime_seven
    have prime_4_eq_11 : Nat.nth Nat.Prime 4 = 11 := Nat.nth_count prime_eleven

    constructor
    -- we'll show that the properties imply that (p, q, r) = (3, 5, 7)
    · intro ⟨hs, hc⟩

      -- let p q r be the kth, (k+1)th and (k+2)th prime, respectively
      obtain ⟨k, k1, k2, k3⟩ := hc
      have hp : Nat.Prime p := by
        rw [←k1]
        exact Nat.prime_nth_prime k
      have hq : Nat.Prime q := by
        rw [←k2]
        exact Nat.prime_nth_prime (k+1)
      have hr : Nat.Prime r := by
        rw [←k3]
        exact Nat.prime_nth_prime (k+2)

      -- if a prime p is larger than 3, then p % 3 = 1 or p % 3 = 2
      have prime_three_lt : ∀ {p : ℕ}, p.Prime → 3 < p → p % 3 = 1 ∨ p % 3 = 2 := by
        intro p ph p3
        -- consider cases of p % 3
        mod_cases p % 3
        -- if p % 3 = 0, then 3 divides 3
        · have dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero H
          -- but both 3 and p are prime, so p must be 3
          have three_prime : Nat.Prime 3 := Nat.prime_three
          have p_eq_three := (Nat.prime_dvd_prime_iff_eq three_prime ph).mp dvd

          -- but 3 < p, contradiction
          rw [p_eq_three] at p3
          linarith only [p3]
        -- other cases work
        · exact Or.inl H
        · exact Or.inr H

      -- if a prime p is larger than 3, then p ^ 2 % = 1
      have prime_three_lt_pow : ∀ {p : ℕ}, p.Prime → 3 < p → p ^ 2 % 3 = 1 := by
        intro p ph p3
        cases' prime_three_lt ph p3 with h1 h2
        · rw [Nat.pow_mod, h1]
        · rw [Nat.pow_mod, h2]

      -- consider cases where k = 0, k = 1 or 1 < k
      rcases lt_trichotomy k 1 with h1 | h2 | h3
      -- when k = 0, we have (p, q, r) = (2, 3, 5)
      · rw [Nat.lt_one_iff] at h1
        subst h1
        simp only [prime_0_eq_2, zero_add, prime_1_eq_3, Nat.nth_count Nat.prime_five] at k1 k2 k3
        rw [prime_2_eq_5] at k3
        rw [←k1, ←k2, ←k3] at hsum

        -- then s = 38
        norm_num at hsum

        -- but 38 is not prime
        have not_prime : ¬Nat.Prime 38 := by decide

        -- contradiction
        rw [hsum] at hs
        contradiction
      -- when k = 0, we have (p, q, r) = (3, 5, 7)
      · subst h2
        simp only [Nat.nth_prime_one_eq_three, Nat.reduceAdd] at k1 k2 k3
        rw [prime_2_eq_5] at k2
        rw [prime_3_eq_7] at k3
        rw [k1, k2, k3]
      -- if 1 < k, then 3 < p, q, r
      · have p_bound : 3 < p := by
          rw [←prime_1_eq_3, ←k1]
          refine (Nat.nth_lt_nth ?_).mpr h3
          exact Nat.infinite_setOf_prime
        have q_bound : 3 < q := by
          refine lt_trans p_bound ?_
          rw [←k1, ←k2]
          refine (Nat.nth_lt_nth ?_).mpr (lt_add_one k)
          exact Nat.infinite_setOf_prime
        have r_bound : 3 < r := by
          refine lt_trans q_bound ?_
          rw [←k2, ←k3]
          refine (Nat.nth_lt_nth ?_).mpr (by omega)
          exact Nat.infinite_setOf_prime

        -- then 3 < s
        have s_bound : 3 < s := by
          rw [hsum]
          -- because 3 < p ^ 2
          have p_sq_bound : 3 < p ^ 2 := by
            refine lt_of_lt_of_le p_bound ?_
            refine Nat.le_self_pow ?_ p
            omega
          apply Nat.lt_add_right
          apply Nat.lt_add_right
          exact p_sq_bound

        -- consider s = p ^ 2 + q ^ 2 + r ^ 2, modulo 3
        apply_fun (· % 3) at hsum

        -- then the RHS is 0
        rw [Nat.add_mod] at hsum
        nth_rw 2 [Nat.add_mod] at hsum
        rw [prime_three_lt_pow hp p_bound,
          prime_three_lt_pow hq q_bound,
          prime_three_lt_pow hr r_bound] at hsum
        norm_num at hsum

        -- but s % 3 is 1 or 2
        have s_mod_three := prime_three_lt hs s_bound

        -- contradiction
        cases' s_mod_three with h1 h2 <;> omega
    -- we'll show that (3, 5, 7) is a valid solution
    · simp only [Prod.mk.injEq, and_imp]
      intro p_eq q_eq r_eq
      subst p_eq q_eq r_eq
      constructor
      -- we have s = 83, which is prime
      · norm_num at hsum
        rw [hsum]
        decide
      -- 3 is the prime with index 1, and the other are consecutive
      · exists 1