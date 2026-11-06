import Mathlib

/- 5. In how many ways can the number 10000 be factored into three natural factors,
none of which is divisible by 10? Factorizations that differ only in the order of the factors are considered the same. -/
theorem number_theory_194242 :
    {(a, b, c) : ℕ × ℕ × ℕ | a ≤ b ∧ b ≤ c ∧  a * b * c = 10000 ∧ ¬10 ∣ a ∧ ¬10 ∣ b ∧ ¬10 ∣ c}.encard = 5 := by

    -- we compute the set directly
    have set_eq: {(a, b, c) : ℕ × ℕ × ℕ | a ≤ b ∧ b ≤ c ∧  a * b * c = 10000 ∧ ¬10 ∣ a ∧ ¬10 ∣ b ∧ ¬10 ∣ c} =
    {(1, 16, 625), (2, 8, 625), (4, 4, 625), (16, 25, 25), (5, 16, 125)} := by

      ext ⟨a, b, c⟩
      constructor
      -- forward direction
      .
        intro h
        simp at *
        rcases h with ⟨lab, lbc, h, ha, hb, hc⟩
        have da: a ∣ 10000 := by
          rw [← h]
          rw [show a * b * c = a * (b * c) by ring]
          simp
        have ua: a ≤ 21 := by  -- we first show a ≤ 21 by inequality
          by_contra! u
          replace u: 22 ≤ a := by omega
          have ub: 22 ≤ b := by omega
          have uc: 22 ≤ c := by omega
          have o: 484 ≤ a * b := by nlinarith
          have p: 10648 ≤ a * b * c := by nlinarith
          rw [h] at p
          norm_num at p
        by_cases va: a = 16
        -- case a = 16
        .
          simp [va] at *
          clear ua va da ha
          replace h: b * c = 625 := by
            nlinarith
          have ob: b ≤ 25 := by nlinarith
          interval_cases b
          all_goals omega

       -- case a ≠ 16, we show that a ≤ 8, then a = 1, 2, 4, 5, or 8
        .
          have u: a ≤ 8 := by
            by_contra! u
            clear * - da u ua ha va
            interval_cases a
            all_goals absurd da; norm_num
            . omega
            . omega
            . omega
          clear va ua
          have v: a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 8 := by
            clear * - u da
            interval_cases a
            all_goals omega
          by_contra! j   -- for convenience, prove by contradiction
          have g1: ¬ 2 ∣ b := by
            by_contra! g
            have f: ¬ 5 ∣ b := by  --then ¬ 5 ∣ b
              by_contra! f
              have h1: 10 ∣ b := by
                rw [show 10 = 2 * 5 by rfl]
                apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
                norm_num
                omega
                omega
              tauto
            -- then we show b ∣ 16
            have db: b ∣ 16 * 625 := by
              norm_num
              rw [← h]
              rw [show a * b * c = b * (a * c) by ring]
              simp
            replace db: b ∣ 16 := by
              have s: Nat.Coprime b 625 := by
                rw [show 625 = 5^4 by rfl]
                apply Nat.Coprime.pow_right
                apply Nat.Coprime.symm
                rw [Nat.Prime.coprime_iff_not_dvd]
                exact f
                norm_num
              apply Nat.Coprime.dvd_of_dvd_mul_right s db
            have va: b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8 ∨ b = 16 := by
              clear * - db
              have h:= db
              apply Nat.le_of_dvd at db
              interval_cases b
              all_goals omega
            rcases va with i | i | i | i | i
            all_goals simp [i] at *
            all_goals clear f da ha g i
            all_goals rcases v with v | v | v | v | v
            all_goals simp [v] at *
            all_goals omega
          -- then we have b ∣ 625
          have db: b ∣ 16 * 625 := by
            norm_num
            rw [← h]
            rw [show a * b * c = b * (a * c) by ring]
            simp
          replace db: b ∣ 5 ^ 4 := by
            have s: Nat.Coprime b 16 := by
              rw [show 16 = 2^4 by rfl]
              apply Nat.Coprime.pow_right
              apply Nat.Coprime.symm
              rw [Nat.Prime.coprime_iff_not_dvd]
              exact g1
              norm_num
            apply Nat.Coprime.dvd_of_dvd_mul_right s db
          rw [Nat.dvd_prime_pow] at db
          obtain ⟨k, hk, n⟩ := db
          replace hk: k ≤ 2 := by  -- hence b = 1, 5 ,25
            by_contra! t
            have o: k = 3 ∨ k = 4 := by omega
            rcases o with o | o
            . simp [o] at n lbc
              simp [n] at h
              have s: 125 ^ 2 ≤ 10000 := by
                calc
                  125 ^ 2 = 15625 := by rfl
                        _ ≤ a * 15625 := by omega
                        _ = a * 125 * 125 := by omega
                        _ ≤ a * 125 * c := by nlinarith
                        _ = 10000 := by rw [h]
              norm_num at s
            . simp [o] at n lbc
              simp [n] at h
              have s: 625 ^ 2 ≤ 10000 := by
                calc
                  625 ^ 2 = 390625 := by rfl
                        _ ≤ a * 390625 := by omega
                        _ = a * 625 * 625 := by omega
                        _ ≤ a * 625 * c := by nlinarith
                        _ = 10000 := by rw [h]
              norm_num at s
          interval_cases k <;> interval_cases a <;> simp at n <;> simp [n] at * <;> omega
          norm_num

      -- backward direction
      .
        intro h
        simp at h
        simp
        rcases h with h | h | h | h | h
        all_goals simp [h]; norm_num

  -- finally, count the set
    rw [set_eq]
    simp [Set.encard]