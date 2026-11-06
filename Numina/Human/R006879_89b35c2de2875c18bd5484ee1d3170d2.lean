import Mathlib

/-Let $m$ be a positive integer such that $m$ is not divisible by 5 and $m$ is not divisible by 11.
Theorem: The set of natural number divisors of $2^{12m}-1$ that are strictly between 60 and 70 is $\{63, 65\}$.-/
theorem divisors_between_60_70 {m : Nat} (hm: m ≥ 1) (h5 : ¬5 ∣ m) (h11 : ¬11 ∣ m) :
  ((Nat.divisors (2^(12*m) - 1)).filter (fun d => 60 < d ∧ d < 70)) = {63, 65} := by
  -- equality of finsets by element-wise reasoning
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton, and_assoc, and_comm]

  -- show 2^12 ≤ 2 ^ (12 * m)
  have: 2^12 ≤ 2 ^ (12 * m):= by
    calc
      _ = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ (12 * m) := Nat.pow_le_pow_right (by omega) (by omega)

  -- show 2 ^ (12 * m) - 1 is odd
  have odd_two_pow_sub_one : Odd (2 ^ (12 * m) - 1) := by
    refine Nat.Even.sub_odd ?_ ?_ ?_
    . omega
    . exact (Nat.even_pow' (by omega)).mpr (by decide)
    . decide

  constructor
  · -- ⇒ direction: any divisor in (60,70) must be 63 or 65
    rintro ⟨hne, hdvd, hgt, hlt⟩

    have h_mod_d: 2 ^ (12 * m) = (1 : ZMod d) := by
      have h_mod_eq_0: (2 ^ (12 * m) - 1 :ℕ) = (0: ZMod d):= (ZMod.natCast_zmod_eq_zero_iff_dvd (2 ^ (12 * m) - 1) d).mpr hdvd

      norm_num at h_mod_eq_0
      calc
        _ = 2 ^ (12 * m) - (1 : ZMod d) + (1 : ZMod d) := by ring_nf
        _ =  (0: ZMod d) + (1 : ZMod d) := by simp [h_mod_eq_0]
        _ = (1 : ZMod d) := by simp

    interval_cases d
    . -- d = 61
      -- consider ZMod 61
      let r := orderOf (2 : ZMod 61)

      haveI : Fact (Nat.Prime 61) := by native_decide

      have h_pow : 2 ^ 60 = (1: ZMod 61) := by
        apply ZMod.pow_card_sub_one_eq_one
        exact Ne.symm (ne_of_beq_false rfl)

      -- check each prime factor of 60 to show orderOf (2 : ZMod 61) = 60
      have h_order_eq_60 : ∀ p, Nat.Prime p → p ∣ 60 → (2 : ZMod 61)^ (60/p) ≠ 1 := by
        intro p hp hdiv
        -- since p ∣ 61, p can only belong to 20.primeFactors
        have h_prime_factors : p ∈ ({2, 3, 5} : Finset ℕ) := by
          rw [show ({2, 3, 5} : Finset ℕ) = Nat.primeFactors 60 by native_decide]
          apply Nat.mem_primeFactors.mpr
          exact ⟨hp, by omega, by omega⟩

        simp only [Finset.mem_insert, Finset.mem_singleton] at h_prime_factors

        rcases h_prime_factors with (h2 | h3 | h5)
        · -- case p = 2
          have : 60/p = 30 := by rw [h2]
          rw [this]
          exact Ne.symm (ne_of_beq_false rfl)
        · -- case p = 3
          have : 60/p = 20 := by rw [h3]
          rw [this]
          exact Ne.symm (ne_of_beq_false rfl)
        · -- case p = 5
          have : 60/p = 12 := by rw [h5]
          rw [this]
          exact Ne.symm (ne_of_beq_false rfl)

      -- show orderOf (2 : ZMod 61) = 60
      have order_eq_60 : r = 60 := orderOf_eq_of_pow_and_pow_div_prime (by positivity) h_pow h_order_eq_60

      -- order must divide 12m
      have h_dvd_12m : 60 ∣ 12 * m := by
        calc _ = orderOf (2 : ZMod 61) := by exact id (Eq.symm order_eq_60)
             _ ∣ 12 * m := orderOf_dvd_iff_pow_eq_one.mpr h_mod_d

      -- 60 = 12 * 5
      rw [show 60 = 12 * 5 by omega] at h_dvd_12m
      have: 5 ∣ m := Nat.dvd_of_mul_dvd_mul_left (by omega) h_dvd_12m

      exact absurd this h5

    . -- d = 62
      -- even number cannot divide odd number
      have : 2 ∣ 2 ^ (12 * m) - 1 := by
        calc
          _ ∣ 62 := by omega
          _ ∣ 2 ^ (12 * m) - 1 := by simp [hdvd]

      exact absurd this (Odd.not_two_dvd_nat odd_two_pow_sub_one)

    . -- d = 63
      exact Or.symm (Or.inr rfl)

    . -- d = 64
      -- even number cannot divide odd number
      have : 2 ∣ 2 ^ (12 * m) - 1 := by
        calc
          _ ∣ 64 := by omega
          _ ∣ 2 ^ (12 * m) - 1 := by simp [hdvd]

      exact absurd this (Odd.not_two_dvd_nat odd_two_pow_sub_one)

    . -- d = 65
      exact Or.symm (Or.inl rfl)

    . -- d = 66
      -- even number cannot divide odd number
      have : 2 ∣ 2 ^ (12 * m) - 1 := by
        calc
          _ ∣ 66 := by omega
          _ ∣ 2 ^ (12 * m) - 1 := by simp [hdvd]

      exact absurd this (Odd.not_two_dvd_nat odd_two_pow_sub_one)

    . -- d = 67
      -- consider ZMod 67
      let r := orderOf (2 : ZMod 67)

      haveI : Fact (Nat.Prime 67) := by native_decide

      have h_pow : 2 ^ 66 = (1: ZMod 67) := by
        apply ZMod.pow_card_sub_one_eq_one
        exact Ne.symm (ne_of_beq_false rfl)

      -- check each prime factor of 66 to show orderOf (2 : ZMod 67) = 66
      have h_order_eq_66 : ∀ p, Nat.Prime p → p ∣ 66 → (2 : ZMod 67)^ (66/p) ≠ 1 := by
        intro p hp hdiv
        -- since p ∣ 61, p can only belong to 20.primeFactors
        have h_prime_factors : p ∈ ({2, 3, 11} : Finset ℕ) := by
          rw [show ({2, 3, 11} : Finset ℕ) = Nat.primeFactors 66 by native_decide]
          apply Nat.mem_primeFactors.mpr
          exact ⟨hp, by omega, by omega⟩

        simp only [Finset.mem_insert, Finset.mem_singleton] at h_prime_factors

        rcases h_prime_factors with (h2 | h3 | h11)
        · -- case p = 2
          have : 66/p = 33 := by rw [h2]
          rw [this]
          exact Ne.symm (ne_of_beq_false rfl)
        · -- case p = 3
          have : 66/p = 22 := by rw [h3]
          rw [this]
          exact Ne.symm (ne_of_beq_false rfl)
        · -- case p = 5
          have : 66/p = 6 := by rw [h11]
          rw [this]
          exact Ne.symm (ne_of_beq_false rfl)

      -- show orderOf (2 : ZMod 67) = 66
      have order_eq_66 : r = 66 := orderOf_eq_of_pow_and_pow_div_prime (by positivity) h_pow h_order_eq_66

      -- order must divide 12m
      have h_dvd_12m : 66 ∣ 12 * m := by
        calc _ = orderOf (2 : ZMod 67) := by exact id (Eq.symm order_eq_66)
             _ ∣ 12 * m := orderOf_dvd_iff_pow_eq_one.mpr h_mod_d

      rw [show 66 = 6 * 11 by omega] at h_dvd_12m
      rw [show 12 * m = 6 * (2 * m) by omega] at h_dvd_12m
      have h_dvd_2m: 11 ∣ 2 * m := Nat.dvd_of_mul_dvd_mul_left (by omega) h_dvd_12m

      have h_dvd_m : 11 ∣ m := by
        have h_dvd_or :11 ∣ 2 ∨ 11 ∣ m := (Nat.Prime.dvd_mul (by decide: Nat.Prime 11)).mp h_dvd_2m
        simp_all
        omega

      exact absurd h_dvd_m h11

    . -- d = 68
      -- even number cannot divide odd number
      have : 2 ∣ 2 ^ (12 * m) - 1 := by
        calc
          _ ∣ 68 := by omega
          _ ∣ 2 ^ (12 * m) - 1 := by simp [hdvd]

      exact absurd this (Odd.not_two_dvd_nat odd_two_pow_sub_one)

    . -- d = 69
      -- consider ZMod 23
      let r := orderOf (2 : ZMod 23)

      have h_pow: 2 ^ 11 = (1: ZMod 23):= by native_decide

      -- check each prime factor of 11 to show orderOf (2 : ZMod 23) = 11
      have h_order_eq_11 : ∀ p, Nat.Prime p → p ∣ 11 → (2 : ZMod 23)^ (11/p) ≠ 1 := by
        intro p hp hdiv
        -- since p ∣ 61, p can only belong to 20.primeFactors
        have h_prime_factors : p ∈ ({11} : Finset ℕ) := by
          rw [show ({11} : Finset ℕ) = Nat.primeFactors 11 by native_decide]
          apply Nat.mem_primeFactors.mpr
          exact ⟨hp, by omega, by omega⟩

        simp only [Finset.mem_insert, Finset.mem_singleton] at h_prime_factors

        rw [h_prime_factors]
        exact Ne.symm (ne_of_beq_false rfl)

      -- show orderOf (2 : ZMod 23) = 11
      have order_eq_66 : r = 11 := orderOf_eq_of_pow_and_pow_div_prime (by positivity) h_pow h_order_eq_11

      have h_mod_d': 2 ^ (12 * m) = (1 : ZMod 23) := by
        have: 23 ∣ 2 ^ (12 * m) - 1 := by
          calc
            _ ∣ 69 := by decide
            _ ∣ 2 ^ (12 * m) - 1 := hdvd

        have h_mod_eq_0: (2 ^ (12 * m) - 1 :ℕ) = (0: ZMod 23):= (ZMod.natCast_zmod_eq_zero_iff_dvd (2 ^ (12 * m) - 1) 23).mpr this

        norm_num at h_mod_eq_0
        calc
          _ = 2 ^ (12 * m) - (1 : ZMod 23) + (1 : ZMod 23) := by ring_nf
          _ =  (0: ZMod 23) + (1 : ZMod 23) := by simp [h_mod_eq_0]
          _ = (1 : ZMod 23) := by simp

      have h_dvd_12m : 11 ∣ 12 * m := by
        calc _ = orderOf (2 : ZMod 23) := by exact id (Eq.symm order_eq_66)
             _ ∣ 12 * m := orderOf_dvd_iff_pow_eq_one.mpr h_mod_d'

      have h_dvd_m : 11 ∣ m := by
        have h_dvd_or :11 ∣ 12 ∨ 11 ∣ m := (Nat.Prime.dvd_mul (by decide: Nat.Prime 11)).mp h_dvd_12m
        simp_all
        omega

      exact absurd h_dvd_m h11

  · -- ⇐ direction: 63 and 65 indeed divide 2^(12*m) - 1
    rintro (h1 | h2)
    · -- case d = 63
      constructor
      . omega
      . constructor
        . -- prove 63 ∣ 2 ^ (12 * m) - 1
          have : 6 ∣ 12 * m := by
            calc
              _ ∣ 12 := by decide
              _ ∣ 12 * m := Nat.dvd_mul_right 12 m

          -- it is sufficient to show 2 ^ 6 = (1: ZMod 63)
          have h_pow : 2 ^ 6 = (1: ZMod 63) := by native_decide
          have h_pow_2:(2: ZMod 63) ^ (12 * m) = (1: ZMod 63) := by
            calc
              _ = (2: ZMod 63) ^ (6 * (2 * m)) := by ring
              _ = ((2: ZMod 63) ^ 6) ^ (2 * m) := by rw [pow_mul]
              _ = 1 ^ (2 * m) := by congr
              _ = 1 := by ring

          have: (2 ^ (12 * m) - 1: ℕ) = (0: ZMod d) := by
            norm_num
            rw [h1]
            exact sub_eq_zero.mpr h_pow_2

          exact (ZMod.natCast_zmod_eq_zero_iff_dvd (2 ^ (12 * m) - 1) d).mp this

        . omega

    · -- case d = 65
      constructor
      . omega
      . constructor
        . -- prove 65 ∣ 2 ^ (12 * m) - 1
          have : 12 ∣ 12 * m := Nat.dvd_mul_right 12 m

          let r := orderOf (2 : ZMod 65)

          -- it is sufficient to show 2 ^ 12 = (1: ZMod 65)
          have h_pow : 2 ^ 12 = (1: ZMod 65) := by native_decide
          have h_pow_2:(2: ZMod 65) ^ (12 * m) = (1: ZMod 65) := by
            calc
              _ = ((2: ZMod 65) ^ 12) ^ m := by rw [pow_mul]
              _ = 1 ^ m := by congr
              _ = 1 := by ring

          have: (2 ^ (12 * m) - 1: ℕ) = (0: ZMod d) := by
            norm_num
            rw [h2]
            exact sub_eq_zero.mpr h_pow_2

          exact (ZMod.natCast_zmod_eq_zero_iff_dvd (2 ^ (12 * m) - 1) d).mp this

        . omega
