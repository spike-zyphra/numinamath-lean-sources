import Mathlib

-- we show a lemma that 2 ^ m % 3 = 1 if m is even
lemma two_pow_odd_mod_three (m: ℕ) (hm: Odd m) : 2 ^ m % 3 = 2 := by
  apply Odd.exists_bit1 at hm
  obtain ⟨k, h⟩ := hm
  simp [h]
  rw [show 2 ^ (2 * k + 1) = 2 ^ (2 * k) * 2 by ring]
  rw [show 2 ^ (2 * k) = (2 ^ 2) ^ k by rw [pow_mul]]
  rw [show 2 ^ 2 = 4 by norm_num]
  rw [Nat.mul_mod]
  rw [Nat.pow_mod]
  simp

/-If a,b are prime numbers, and
p = a ^ b + b ^ a is also a prime number, then
p equals (A) 17 (B) 13 (C) 11 (D) 19-/

theorem number_theory_179555 {p a b: ℕ} (hp: Nat.Prime p) (ha: Nat.Prime a) (hb: Nat.Prime b)
   (h: p = a ^ b + b ^ a): p = 17 := by

    have la: 2 ≤ a := by
      apply Nat.Prime.two_le ha
    have lb: 2 ≤ b := by
      apply Nat.Prime.two_le hb

    -- we show that one of a and b is 2
    have r: a = 2 ∨ b = 2 := by
      by_contra! o
      rcases o with ⟨oa, ob⟩
      replace oa: Odd a := by
        apply Nat.Prime.odd_of_ne_two ha oa
      replace ob: Odd b := by
        apply Nat.Prime.odd_of_ne_two hb ob
      replace oa: Odd (a ^ b) := by
        apply Odd.pow
        exact oa
      replace ob: Odd (b ^ a) := by
        apply Odd.pow
        exact ob
      -- then p is even
      have ep: Even p := by
        rw [h]
        rw [Nat.even_add']
        simp [oa, ob]
      rw [Nat.Prime.even_iff hp] at ep
      simp [ep] at h
      have i: 0 < a ^ b := by
        apply Nat.pos_pow_of_pos
        linarith
      have j: 0 < b ^ a := by
        apply Nat.pos_pow_of_pos
        linarith
      have u: a ^ b = 1 := by omega
      have v: b ^ a = 1 := by omega
      rw [pow_eq_one_iff_of_nonneg] at u
      simp [u] at ha
      norm_num at ha
      omega
      omega

    -- then we check r by_cases
    rcases r with r | r

    -- case a = 2
    .
      simp [r] at *
      clear ha la r
      by_cases o: Even b

      -- case 1: b is even
      .
        rw [Nat.Prime.even_iff hb] at o
        simp [o] at h
        simp [h] at hp
        norm_num at hp

      -- case 2: b is odd
      .
        simp at o
        by_cases d: b = 3

        -- case 2.1 : b = 3
        .
          simp [d] at h
          exact h

        -- case 2.2 : b is odd and not 3
        .
          -- then we show that 3 ∣ p
          have c: 3 ∣ p := by
            rw [h]
            apply Nat.dvd_of_mod_eq_zero
            rw [Nat.add_mod]
            have i:= two_pow_odd_mod_three b o
            rw [i]
            have j: b ^ 2 % 3 = 1 := by
              rw [Nat.pow_mod]
              have g: b % 3 ≠ 0 := by
                by_contra! g
                apply Nat.dvd_of_mod_eq_zero at g
                rw [Nat.prime_dvd_prime_iff_eq] at g
                simp [← g] at d
                norm_num
                exact hb
              have v: b % 3 = 1 ∨ b % 3 = 2 := by omega
              rcases v with v | v
              .
                simp [v]
              .
                simp [v]
            rw [j]

          -- then p = 3
          rw [Nat.prime_dvd_prime_iff_eq] at c
          simp [← c] at h
          have s: 4 ≤ b ^ 2 := by nlinarith
          have t: 0 < 2 ^ b := by
            apply Nat.pos_pow_of_pos
            linarith
          nlinarith
          norm_num
          exact hp


    -- case b = 2, just similar as above
    .
      simp [r] at *
      clear hb lb r
      by_cases o: Even a

      -- case 1: a is even
      .
        rw [Nat.Prime.even_iff ha] at o
        simp [o] at h
        simp [h] at hp
        norm_num at hp

      -- case 2: a is odd
      .
        simp at o
        by_cases d: a = 3

        -- case 2.1 : a = 3
        .
          simp [d] at h
          exact h

        -- case 2.2 : a is odd and not 3
        .
          -- then we show that 3 ∣ p
          have c: 3 ∣ p := by
            rw [h]
            apply Nat.dvd_of_mod_eq_zero
            rw [Nat.add_mod]
            have i:= two_pow_odd_mod_three a o
            rw [i]
            have j: a ^ 2 % 3 = 1 := by
              rw [Nat.pow_mod]
              have g: a % 3 ≠ 0 := by
                by_contra! g
                apply Nat.dvd_of_mod_eq_zero at g
                rw [Nat.prime_dvd_prime_iff_eq] at g
                simp [← g] at d
                norm_num
                exact ha
              have v: a % 3 = 1 ∨ a % 3 = 2 := by omega
              rcases v with v | v
              .
                simp [v]
              .
                simp [v]
            rw [j]

          -- then p = 3
          rw [Nat.prime_dvd_prime_iff_eq] at c
          simp [← c] at h
          have s: 4 ≤ a ^ 2 := by nlinarith
          have t: 0 < 2 ^ a := by
            apply Nat.pos_pow_of_pos
            linarith
          nlinarith
          norm_num
          exact hp
          
