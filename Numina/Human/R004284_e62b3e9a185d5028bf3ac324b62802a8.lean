import Mathlib

set_option maxHeartbeats 250000 -- The long proof requires a higher value for maxHeartbeats

/- Prove that for every nonnegative integer $n$, the number $7^{7^{n}}+1$ is
   the product of at least $2 n+3$ (not necessarily distinct) primes.

   Note that the number of prime factors (not necessarily distinct)
   of a positive m ∈ ℕ is given by ∑ p ∈ m.primeFactors, m.factorization p.
   -/
theorem number_theory_248425 (n : ℕ) :
  ∑ p ∈ (7^(7^n)+1).primeFactors, (7^(7^n)+1).factorization p ≥ 2 * n + 3 := by

  -- We show that if a, b ∈ ℕ are positive, then
  -- ∑ p ∈ (a * b).primeFactors, (a * b).factorization p ≥ ∑ p ∈ a.primeFactors, a.factorization p + ∑ p ∈ b.primeFactors, b.factorization p
  have facnum (a b : ℕ) (ha : a > 0) (hb : b > 0) : ∑ p ∈ (a * b).primeFactors, (a * b).factorization p
      ≥ ∑ p ∈ a.primeFactors, a.factorization p + ∑ p ∈ b.primeFactors, b.factorization p
      := by
    -- First, it is known that with a > 0 and b > 0,
    -- (a * b).factorization = a.factorization + b.factorization p.
    rw [Nat.factorization_mul (by omega) (by omega)]
    -- Thus, ∑ p ∈ (a * b).primeFactors, (a * b).factorization p
    -- = ∑ p ∈ (a * b).primeFactors, (a.factorization + b.factorization) p
    -- = ∑ p ∈ (a * b).primeFactors, a.factorization p + ∑ p ∈ (a * b).primeFactors, b.factorization) p
    calc
      _ = ∑ p ∈ (a * b).primeFactors, (a.factorization p + b.factorization p) := by
            apply Finset.sum_congr rfl; simp
      _ = ∑ p ∈ (a * b).primeFactors, a.factorization p
          + ∑ p ∈ (a * b).primeFactors, b.factorization p := by rw [Finset.sum_add_distrib]
      _ ≥ _ := by
        obtain h := @Nat.primeFactors_mul a b (by omega) (by omega)
        apply Nat.add_le_add
        . -- But a.primeFactors ⊆ (a * b).primeFactors
          have asub : a.primeFactors ⊆ (a * b).primeFactors := by rw [h]; exact Finset.subset_union_left
          apply Finset.sum_le_sum_of_subset asub
        . -- and b.primeFactors ⊆ (a * b).primeFactors
          have bsub : b.primeFactors ⊆ (a * b).primeFactors := by rw [h]; exact Finset.subset_union_right
          -- Hence, the sum is at least ∑ p ∈ a.primeFactors, a.factorization p + ∑ p ∈ b.primeFactors, b.factorization p
          apply Finset.sum_le_sum_of_subset bsub

  -- We prove the statement by induction on n.
  induction n with
  | zero => -- When n = 0, the statement reduces to 3 ≤ ∑ x ∈ Nat.primeFactors 8, (Nat.factorization 8) x
    simp
    -- Rewrite 8 as 2 ^ 3.
    have : 8 = 2 ^ 3 := by norm_num
    rw [this]
    -- Since 2 is a prime, the set of primes that divide 2 ^ 3 consists of just the prime 2.
    rw [Nat.primeFactors_prime_pow (by simp) Nat.prime_two]
    -- Also, the multiplicity of 2 in 8 is 3 times the multplicity of 2 in 2.
    rw [Nat.factorization_pow]
    -- The rest follows from a simple calculation.
    norm_num
  | succ k ih  =>

    -- Note that 7 ^ k + 1 is Even.
    have : Even (7 ^ k + 1) := by rw [@Nat.even_add_one]
                                  simp
                                  apply Odd.pow
                                  decide

    -- Write 7 ^ k + 1 as m + m for some m ∈ ℕ.
    obtain ⟨ m, hm ⟩ := this

    -- Our first claim is that (7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) ≥ 2
    have claim1 : (7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) ≥ 2 := by
        -- Note that (7 ^ 7 ^ k + 1) - 7 ^ m ≥ 1
        have ineq1 : (7 ^ 7 ^ k + 1) - 7 ^ m ≥ 1 := by
          suffices 7 * ((7 ^ 7 ^ k + 1) - 7 ^ m) ≥ 7 * 1 by apply Nat.le_of_mul_le_mul_left
                                                            . exact this
                                                            . norm_num
          calc
            _ = 7 * (7 ^ 7 ^ k + 1) - 7 * 7 ^ m := by rw [Nat.mul_sub]
            _ = 7 ^ (7 ^ k + 1) + 7 * 1 - 7 ^ (m + 1) := by ring_nf
            _ ≥ 7 * 1 := by suffices 7 ^ (7 ^ k + 1) ≥ 7 ^ (m + 1) by apply Nat.le_sub_of_add_le
                                                                      rw [add_comm]
                                                                      exact Nat.add_le_add_right this (7 * 1)
                            rw [hm]
                            suffices m + m ≥ m + 1 by apply Nat.pow_le_pow_of_le_right; norm_num; exact this
                            by_cases g : m < 1
                            . simp at g; rw [g] at hm; simp at hm
                            . simp at g
                              apply Nat.add_le_add_left
                              exact Nat.one_le_iff_ne_zero.mpr g

        -- Note also that (7 ^ 7 ^ k + 1) ^ 2 ≥ (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)
        have ineq2 : (7 ^ 7 ^ k + 1) ^ 2 ≥ (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) := by
          calc
            _ = 7 ^ (2 * 7 ^ k) + 1 + 2 * 7 ^ 7 ^ k := by ring
            _ ≥ 7 ^ (2 * 7 ^ k) + 1 + 7 ^ 7 ^ k := by apply Nat.add_le_add_left; rw [Nat.two_mul]; apply Nat.le_add_right
            _ = _ := by ring

        -- Hence, (7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)
        -- = (7 ^ 7 ^ k + 1) * (7 ^ 7 ^ k + 1) ^ 2 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)
        -- ≥ (7 ^ 7 ^ k + 1) * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)
        -- ≥ (7 ^ 7 ^ k + 1 - 7 ^ m) * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)
        -- ≥ 7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1 ≥ 2
        calc
          _ = (7 ^ 7 ^ k + 1) * (7 ^ 7 ^ k + 1) ^ 2 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) := by ring_nf
          _ ≥ (7 ^ 7 ^ k + 1) * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) := by
                  apply Nat.sub_le_sub_right
                  apply Nat.mul_le_mul_left; exact ineq2
          _ = ((7 ^ 7 ^ k + 1) - 7 ^ m) * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) := by rw [Nat.sub_mul]
          _ ≥ 1 * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) := by apply Nat.mul_le_mul_right; exact ineq1
          _ = 7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1 := by rw [one_mul]
          _ ≥ 2 := by simp; apply Nat.le_add_right_of_le; apply Nat.one_le_pow'

    -- Our second claim is that (7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) ≥ 2.
    -- This follows easily from that (7 ^ 7 ^ k + 1) ^ 3 ≥ 1 and 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) ≥ 1.
    have claim2 : (7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) ≥ 2 := by
      have ineq1 : (7 ^ 7 ^ k + 1) ^ 3 ≥ 1 := by exact NeZero.one_le
      have ineq2 : 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) ≥ 1 := by exact NeZero.one_le
      exact Nat.add_le_add ineq1 ineq2

    -- We check that 7 ^ 7 ^ (k + 1) + 1 factors as
    -- (7 ^ 7 ^ k  + 1)
    --  * ((7 ^ 7 ^ k + 1)^3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))
    --  * ((7 ^ 7 ^ k + 1)^3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))
    have factoring :   (7 ^ 7 ^ (k + 1) + 1)
           =   (7 ^ 7 ^ k  + 1)
             * ((7 ^ 7 ^ k + 1)^3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))
             * ((7 ^ 7 ^ k + 1)^3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)) := by
                have : ((7 ^ 7 ^ k + 1)^3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))
                  * ((7 ^ 7 ^ k + 1)^3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))
                  = ((7 ^ 7 ^ k + 1)^3)^2 - (7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))^2 := by
                      rw [mul_comm]; rw [← Nat.sq_sub_sq];
                rw [mul_assoc, this, Nat.mul_sub]
                symm
                rw [Nat.sub_eq_iff_eq_add]
                . rw [mul_pow]
                  rw [← pow_mul 7 m 2]
                  ring_nf at hm
                  rw [← hm]
                  ring_nf
                . apply Nat.mul_le_mul_left
                  apply Nat.pow_le_pow_of_le_left
                  rw [← ge_iff_le]
                  calc
                    _ = (7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) := by
                          rw [Nat.sub_add_cancel]
                          have g : (7 ^ 7 ^ k + 1) ^ 3 > 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) := by
                            have : (7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1) > 0 := by
                              calc
                                _ ≥ 2 := by exact claim1
                                _ > 0 := by exact Nat.zero_lt_two
                            simp [Nat.sub_pos_iff_lt] at this
                            exact this
                          exact le_of_lt g
                    _ ≥ _ := by apply Nat.le_add_left

    -- Rewrite 7 ^ 7 ^ (k + 1) + 1 in the goal with the above factoring.
    rw [factoring]

    -- Apply facnum twice to
    -- ∑ p ∈ ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)) * ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).primeFactors,
    --       ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)) * ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).factorization p
    have t1 :
       ∑ p ∈ ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)) * ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).primeFactors,
             ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)) * ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).factorization p
        ≥ ∑ p ∈ ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).primeFactors,
            ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).factorization p
            + ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
            ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p := by apply facnum
                                                                                                    . apply Nat.mul_pos
                                                                                                      . simp
                                                                                                      . linarith
                                                                                                    . simp

    have t2 :
          ∑ p ∈ ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).primeFactors,
            ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).factorization p
            + ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
            ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p
        ≥ ∑ p ∈ (7 ^ 7 ^ k + 1).primeFactors, (7 ^ 7 ^ k + 1).factorization p
          + ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
                  ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p
          + ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
            ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p := by
              apply Nat.add_le_add_right
              apply facnum
              . simp
              . linarith

    rw [ge_iff_le] at t1 t2

    -- We obtain that
    -- ∑ p ∈ (7 ^ 7 ^ k + 1).primeFactors, (7 ^ 7 ^ k + 1).factorization p +
    -- ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
    --    ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p +
    -- ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
    --    ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p ≤
    -- ∑ p ∈ ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)) *
    --    ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).primeFactors,
    --   ((7 ^ 7 ^ k + 1) * ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)) *
    --       ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1))).factorization p
    obtain t3 := LE.le.trans t2 t1
    clear t1 t2
    rw [← ge_iff_le] at t3

    -- Now, we have
    -- ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
    --       ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p ≥ 1
    have t4 : ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
                ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p ≥ 1 := by
                let r := (7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)
                have : r.minFac ∈ r.primeFactors := by
                  simp [r];
                  constructor
                  . apply Nat.minFac_prime
                    linarith
                  . constructor
                    . apply Nat.minFac_dvd
                    . linarith
                calc
                  _ ≥ ∑ p ∈ { r.minFac }, r.factorization p := by apply Finset.sum_le_sum_of_subset; simp [this]
                  _ = r.factorization r.minFac := by exact rfl
                  _ ≥ 1 := by refine (Nat.Prime.dvd_iff_one_le_factorization ?_ ?_).mp ?_
                              . exact Nat.prime_of_mem_primeFactors this
                              . linarith
                              . exact Nat.minFac_dvd r

    -- and
    --  ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
    --        ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p ≥ 1
    have t5 : ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
                ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p ≥ 1 := by
                let r := (7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)
                have : r.minFac ∈ r.primeFactors := by
                  simp [r];
                  constructor
                  . apply Nat.minFac_prime
                    linarith
                  . apply Nat.minFac_dvd
                calc
                  _ ≥ ∑ p ∈ { r.minFac }, r.factorization p := by apply Finset.sum_le_sum_of_subset; simp [this]
                  _ = r.factorization r.minFac := by exact rfl
                  _ ≥ 1 := by refine (Nat.Prime.dvd_iff_one_le_factorization ?_ ?_).mp ?_
                              . exact Nat.prime_of_mem_primeFactors this
                              . exact Nat.not_eq_zero_of_lt claim2
                              . exact Nat.minFac_dvd r

    -- These inequalities together with the induction hypothesis gives the desired inequality.
    calc
      _ ≥ ∑ p ∈ (7 ^ 7 ^ k + 1).primeFactors, (7 ^ 7 ^ k + 1).factorization p +
          ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
              ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p +
          ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
            ((7 ^ 7 ^ k + 1) ^ 3 + 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p := by exact t3
      _ ≥ ∑ p ∈ (7 ^ 7 ^ k + 1).primeFactors, (7 ^ 7 ^ k + 1).factorization p +
          ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
              ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p + 1 := by apply Nat.add_le_add_left t5
      _ = 1 + ∑ p ∈ (7 ^ 7 ^ k + 1).primeFactors, (7 ^ 7 ^ k + 1).factorization p +
          ∑ p ∈ ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).primeFactors,
              ((7 ^ 7 ^ k + 1) ^ 3 - 7 ^ m * (7 ^ (2 * 7 ^ k) + 7 ^ 7 ^ k + 1)).factorization p := by ring
      _ ≥ 1 + ∑ p ∈ (7 ^ 7 ^ k + 1).primeFactors, (7 ^ 7 ^ k + 1).factorization p + 1 := by apply Nat.add_le_add_left t4
      _ = 2 + ∑ p ∈ (7 ^ 7 ^ k + 1).primeFactors, (7 ^ 7 ^ k + 1).factorization p := by ring
      _ ≥ 2 + (2 * k + 3) := by apply Nat.add_le_add_left ih
      _ = 2 * (k + 1) + 3 := by ring
