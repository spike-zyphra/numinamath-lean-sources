import Mathlib

/- Find all prime numbers p,q and r that satisfy the equation:
p ^ q + q ^ p = r -/

theorem number_theory_178104 :
  {(p, q, r): ℕ × ℕ × ℕ | Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p ^ q + q ^ p = r} =
    {(2, 3, 17), (3, 2, 17)} := by

    ext ⟨p, q, r⟩
    constructor
    -- the forward direction
    .
      intro h
      simp at h
      simp
      rcases h with ⟨hp, hq, hr, h⟩
      by_cases l: p ≤ q

      -- case 1: p ≤ q
      .
        left
        -- then we can show that p = 2
        have ep: p = 2 := by
          by_contra! o
          have op: Odd p := by
            apply Nat.Prime.odd_of_ne_two
            exact hp
            exact o
          have oq: Odd q := by
            apply Nat.Prime.odd_of_ne_two
            exact hq
            by_contra! f
            rw [f] at l
            interval_cases p
            all_goals norm_num at hp
            norm_num at o
          replace op: Odd (p ^ q) := by
            apply Odd.pow
            exact op
          replace oq: Odd (q ^ p) := by
            apply Odd.pow
            exact oq
          have er: Even r := by
            rw [← h]
            rw [Nat.even_add']
            simp [op, oq]
          rw [Nat.Prime.even_iff] at er
          simp [er] at h
          have lp: 2 ≤ p := by
            by_contra! f
            interval_cases p
            all_goals norm_num at hp
          have lq: 2 ≤ q := by
            by_contra! f
            interval_cases q
            all_goals norm_num at hq
          have l1: 4 ≤ p ^ q := by
            calc
              4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ q := by apply Nat.pow_le_pow_of_le_right; norm_num; linarith
              _ ≤ p ^ q := by apply Nat.pow_le_pow_left; linarith
          omega
          exact hr
        simp [ep] at *
        clear hp ep

        -- then we show that q = 3
        have eq: q = 3 := by
          by_contra! u
          replace l: 4 ≤ q := by
            have i: q ≠ 2 := by
              by_contra! i
              simp [i] at h
              simp [← h] at hr
              norm_num at hr
            omega
          clear u
          -- we show 3 ∣ r to derive a contradiction
          have c: 3 ∣ r := by
            rw [← h]
            have eq: 2 ^ q + q ^ 2 = 2 ^ q + 1 + (q ^ 2 - 1) := by
              have l: 1 ≤ q ^ 2 := by
                calc
                  1 = 1 ^ 2 := by norm_num
                  _ ≤ q ^ 2 := by apply Nat.pow_le_pow_left; linarith
              omega
            rw [eq]
            clear eq
            apply Nat.dvd_add
            .
              have oq: Odd q := by
                apply Nat.Prime.odd_of_ne_two
                exact hq
                omega
              zify
              apply Int.dvd_of_emod_eq_zero
              rw [Int.add_emod]
              rw [show (1: ℤ) % 3 = 1 by norm_num]
              have v: (2: ℤ) ^ q % 3 = 2 := by
                nth_rewrite 2 [show (2: ℤ) = (-1) % 3 by norm_num]
                rw [show (3: ℤ) = ↑(3: ℕ) by norm_num]
                rw [← ZMod.intCast_eq_intCast_iff']
                rw [ZMod.intCast_eq_intCast_iff]
                have eq: -1 = (-1) ^ q := by
                  symm
                  apply Odd.neg_one_pow
                  exact oq
                rw [eq]
                apply Int.ModEq.pow
                norm_num
                decide
              rw [v]
              norm_num
            .
              apply Nat.dvd_of_mod_eq_zero
              apply Nat.sub_mod_eq_zero_of_mod_eq
              rw [show q ^ 2 = q * q by ring]
              rw [Nat.mul_mod]
              have o: q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
              rcases o with o | o | o
              .
                rw [← Nat.dvd_iff_mod_eq_zero] at o
                rw [Nat.prime_dvd_prime_iff_eq] at o
                simp [← o] at l
                norm_num
                exact hq
              .
                simp [o]
              .
                simp [o]
          -- now r must be 3
          rw [Nat.prime_dvd_prime_iff_eq] at c
          simp [← c] at h
          have l: 2 ^ 4 ≤ 2 ^ q := by
            apply Nat.pow_le_pow_of_le_right
            norm_num
            linarith
          nlinarith
          norm_num
          exact hr

        -- finally, we get r = 17
        simp [eq] at *
        rw [← h]

      -- case 2: q ≤ p, just the same as above
      .
        right
        -- then we can show that q = 2
        have eq: q = 2 := by
          by_contra! o
          have oq: Odd q := by
            apply Nat.Prime.odd_of_ne_two
            exact hq
            exact o
          have op: Odd p := by
            apply Nat.Prime.odd_of_ne_two
            exact hp
            by_contra! f
            rw [f] at l
            interval_cases q
            all_goals norm_num at hq
          replace op: Odd (p ^ q) := by
            apply Odd.pow
            exact op
          replace oq: Odd (q ^ p) := by
            apply Odd.pow
            exact oq
          have er: Even r := by
            rw [← h]
            rw [Nat.even_add']
            simp [op, oq]
          rw [Nat.Prime.even_iff] at er
          simp [er] at h
          have lp: 2 ≤ p := by
            by_contra! f
            interval_cases p
            all_goals norm_num at hp
          have lq: 2 ≤ q := by
            by_contra! f
            interval_cases q
            all_goals norm_num at hq
          have l1: 4 ≤ p ^ q := by
            calc
              4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ q := by apply Nat.pow_le_pow_of_le_right; norm_num; linarith
              _ ≤ p ^ q := by apply Nat.pow_le_pow_left; linarith
          omega
          exact hr
        simp [eq] at *
        clear hq eq

        -- then we show that p = 3
        have ep: p = 3 := by
          by_contra! u
          replace l: 4 ≤ p := by
            have i: p ≠ 2 := by
              by_contra! i
              simp [i] at h
              simp [← h] at hr
              norm_num at hr
            omega
          clear u
          -- we show 3 ∣ r to derive a contradiction
          have c: 3 ∣ r := by
            rw [← h]
            have eq: p ^ 2 + 2 ^ p = 2 ^ p + 1 + (p ^ 2 - 1) := by
              have l: 1 ≤ p ^ 2 := by
                calc
                  1 = 1 ^ 2 := by norm_num
                  _ ≤ p ^ 2 := by apply Nat.pow_le_pow_left; linarith
              omega
            rw [eq]
            clear eq
            apply Nat.dvd_add
            .
              have op: Odd p := by
                apply Nat.Prime.odd_of_ne_two
                exact hp
                omega
              zify
              apply Int.dvd_of_emod_eq_zero
              rw [Int.add_emod]
              rw [show (1: ℤ) % 3 = 1 by norm_num]
              have v: (2: ℤ) ^ p % 3 = 2 := by
                nth_rewrite 2 [show (2: ℤ) = (-1) % 3 by norm_num]
                rw [show (3: ℤ) = ↑(3: ℕ) by norm_num]
                rw [← ZMod.intCast_eq_intCast_iff']
                rw [ZMod.intCast_eq_intCast_iff]
                have eq: -1 = (-1) ^ p := by
                  symm
                  apply Odd.neg_one_pow
                  exact op
                rw [eq]
                apply Int.ModEq.pow
                norm_num
                decide
              rw [v]
              norm_num
            .
              apply Nat.dvd_of_mod_eq_zero
              apply Nat.sub_mod_eq_zero_of_mod_eq
              rw [show p ^ 2 = p * p by ring]
              rw [Nat.mul_mod]
              have o: p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
              rcases o with o | o | o
              .
                rw [← Nat.dvd_iff_mod_eq_zero] at o
                rw [Nat.prime_dvd_prime_iff_eq] at o
                simp [← o] at l
                norm_num
                exact hp
              .
                simp [o]
              .
                simp [o]
          -- now r must be 3
          rw [Nat.prime_dvd_prime_iff_eq] at c
          simp [← c] at h
          have l: 2 ^ 4 ≤ 2 ^ p := by
            apply Nat.pow_le_pow_of_le_right
            norm_num
            linarith
          nlinarith
          norm_num
          exact hr

        -- finally, we get r = 17
        simp [ep] at *
        rw [← h]


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h
      .
        simp [h]
        norm_num
      .
        simp [h]
        norm_num

