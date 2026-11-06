import Mathlib

set_option maxHeartbeats 400000
/-A prime number p is mundane if there exist positive integers a and b less than p/2
such that ab-1 /p is a positive integer. Find, with proof, all prime numbers that
are not mundane-/
theorem number_theory_610623: {p: ℕ | Nat.Prime p ∧ ¬ ∃ a b: ℕ, 0 < a ∧ 0 < b ∧ a < (p: ℚ) / 2 ∧ b < (p: ℚ) / 2 ∧
p ∣ (a * b - 1) ∧ a * b - 1 > 0} = {2, 3, 5, 7 ,13} := by
  ext p
  simp only [Set.mem_setOf_eq]
  constructor
  -- the forward direction
  . intro h
    simp
    -- we show that p ≤ 16
    have l: p ≤ 16 := by
      by_contra! l
      replace l: 17 ≤ p := by omega
      rcases h with ⟨prime_p,h⟩
      absurd h
      have mod9: p % 9 = 1 ∨ p % 9 = 2 ∨ p % 9 = 4 ∨ p % 9 = 5 ∨ p % 9 = 7 ∨ p % 9 = 8 := by
        by_contra! no
        replace no: p % 9 = 0 ∨ p % 9 = 3 ∨ p % 9 = 6 := by omega
        rcases no with no | no | no
        . replace no: 9 ∣ p := by omega
          rw [Nat.Prime.dvd_iff_eq] at no
          omega
          exact prime_p
          norm_num
        . replace no: 3 ∣ p := by omega
          rw [Nat.Prime.dvd_iff_eq] at no
          omega
          exact prime_p
          norm_num
        . replace no: 3 ∣ p := by omega
          rw [Nat.Prime.dvd_iff_eq] at no
          omega
          exact prime_p
          norm_num
      rcases mod9 with mod9 | mod9 | mod9 | mod9 | mod9 | mod9
      -- case: p % 9 = 1
      . replace mod9: 9 ∣ p - 1 := by omega
        have mod9':= mod9
        apply exists_eq_mul_right_of_dvd at mod9
        obtain ⟨k,hk⟩ := mod9
        have dk: 2 ∣ k := by
          by_contra! no
          replace no: 2 ∣ k - 1 := by omega
          apply exists_eq_mul_right_of_dvd at no
          obtain ⟨m,hm⟩ := no
          replace hm : k = 2 * m + 1 := by omega
          simp [hm] at hk
          replace hk: p = 2 * (9 * m + 5) := by omega
          have lp: 2 ∣ p := by rw [hk]; omega
          rw [Nat.Prime.dvd_iff_eq] at lp
          omega
          exact prime_p
          norm_num
        apply exists_eq_mul_right_of_dvd at dk
        obtain ⟨m,hm⟩ := dk
        replace hk: p = 18 * m + 1 := by omega
        have o: 1 ≤ m := by omega
        use 4 * m
        use 9 * m - 4
        simp
        constructor
        . omega
        . constructor
          . by_contra! no
            replace no: ↑p ≤ (18: ℚ) := by linarith
            simp at no
            replace no: p = 17 ∨ p = 18 := by omega
            rcases no with no | no
            . simp [no] at mod9'
              tauto
            . rw [no] at prime_p
              tauto
          . constructor
            . ring_nf
              simp [hk]
              have o: 1 ≤ m := by omega
              qify at o
              nlinarith
            . constructor
              . simp [hk]
                ring_nf
                have i: ↑(m * (9: ℕ) - 4) = (m: ℚ) * 9 - 4 := by
                  rw [Nat.cast_sub]
                  simp
                  omega
                rw [i]
                nlinarith
              . constructor
                . ring_nf
                  simp [hk]
                  have i: m * (m * 9 - 4) * 4 - 1 = (18 * m + 1) * (2 * m - 1) := by
                    ring_nf
                    zify
                    have i1: ↑(m * ((m: ℕ) * 9 - 4) * 4 - 1) = (m * ((m: ℤ) * 9 - 4) * 4 - 1) := by
                      rw [Nat.cast_sub]
                      simp
                      left
                      rw [Nat.cast_sub]
                      simp
                      omega
                      qify
                      rw [Nat.cast_sub]
                      simp
                      qify at o
                      nlinarith
                      omega
                    rw [i1]
                    rw [Nat.cast_sub]
                    simp
                    ring_nf
                    omega
                  rw [i]
                  apply Nat.dvd_mul_right
                . zify
                  rw [Nat.cast_sub]
                  simp
                  nlinarith
                  omega
      -- case: p % 9 = 2
      . replace mod9: 9 ∣ p - 2 := by omega
        have mod9':= mod9
        apply exists_eq_mul_right_of_dvd at mod9
        obtain ⟨k,hk⟩ := mod9
        replace hk: p = 9 * k + 2 := by omega
        use 4 * k + 1
        use 9
        simp
        constructor
        . simp [hk]
          have o: 2 ≤ k := by omega
          qify at o
          nlinarith
        . constructor
          . by_contra! no
            replace no: ↑p ≤ (18: ℚ) := by linarith
            simp at no
            replace no: p = 17 ∨ p = 18 := by omega
            rcases no with no | no
            . simp [no] at mod9'
              tauto
            . rw [no] at prime_p
              tauto
          . constructor
            . ring_nf
              rw [show 9 + k * 36 - 1 = 4 * (9 * k + 2) by omega]
              rw [← hk]
              apply Nat.dvd_mul_left
            . omega
     -- cases p % 9 = 4
      . replace mod9: 9 ∣ p - 4 := by omega
        have mod9':= mod9
        apply exists_eq_mul_right_of_dvd at mod9
        obtain ⟨k,hk⟩ := mod9
        replace hk: p = 9 * k + 4 := by omega
        use 2 * k + 1
        use 9
        simp
        constructor
        . simp [hk]
          have o: 2 ≤ k := by omega
          qify at o
          nlinarith
        . constructor
          . by_contra! no
            replace no: ↑p ≤ (18: ℚ) := by linarith
            simp at no
            replace no: p = 17 ∨ p = 18 := by omega
            rcases no with no | no
            . simp [no] at mod9'
              tauto
            . rw [no] at prime_p
              tauto
          . constructor
            . ring_nf
              rw [show 9 + k * 18 - 1 = 2 * (9 * k + 4) by omega]
              rw [← hk]
              apply Nat.dvd_mul_left
            . omega
    -- case: p % 9 = 5
      . by_cases y: p ≠ 23
        -- for p ≠ 23
        . replace mod9: 9 ∣ p - 5 := by omega
          have mod9':= mod9
          apply exists_eq_mul_right_of_dvd at mod9
          obtain ⟨k,hk⟩ := mod9
          replace hk: p = 9 * k + 5 := by omega
          have dk: 2 ∣ k := by
              by_contra! no
              replace no: 2 ∣ k - 1 := by omega
              apply exists_eq_mul_right_of_dvd at no
              obtain ⟨m,hm⟩ := no
              replace hm : k = 2 * m + 1 := by omega
              simp [hm] at hk
              replace hk: p = 2 * (9 * m + 7) := by omega
              have lp: 2 ∣ p := by rw [hk]; omega
              rw [Nat.Prime.dvd_iff_eq] at lp
              omega
              exact prime_p
              norm_num
          apply exists_eq_mul_right_of_dvd at dk
          obtain ⟨m,hm⟩ := dk
          replace hk: p = 18 * m + 5 := by omega
          have o: 2 ≤ m := by omega
          use 7 * m + 2
          use 18
          simp
          constructor
          . simp [hk]
            have o: 2 ≤ k := by omega
            qify at o
            nlinarith
          . constructor
            . by_contra! no
              rw [hk] at no
              rw [Nat.cast_add] at no
              absurd no
              simp
              qify at o
              nlinarith
            . constructor
              . ring_nf
                rw [show 36 + m * 126 - 1 = 7 * (18 * m + 5) by omega]
                rw [← hk]
                apply Nat.dvd_mul_left
              . omega
        -- for p = 23
        . simp at y
          use 4
          use 6
          simp [y]
          norm_num
     -- case: p % 9 = 7
      . replace mod9: 9 ∣ p - 7 := by omega
        have mod9':= mod9
        apply exists_eq_mul_right_of_dvd at mod9
        obtain ⟨k,hk⟩ := mod9
        replace hk: p = 9 * k + 7 := by omega
        have dk: 2 ∣ k := by
              by_contra! no
              replace no: 2 ∣ k - 1 := by omega
              apply exists_eq_mul_right_of_dvd at no
              obtain ⟨m,hm⟩ := no
              replace hm : k = 2 * m + 1 := by omega
              simp [hm] at hk
              replace hk: p = 2 * (9 * m + 8) := by omega
              have lp: 2 ∣ p := by rw [hk]; omega
              rw [Nat.Prime.dvd_iff_eq] at lp
              omega
              exact prime_p
              norm_num
        apply exists_eq_mul_right_of_dvd at dk
        obtain ⟨m,hm⟩ := dk
        replace hk: p = 18 * m + 7 := by omega
        have ne: m ≠ 1 := by
          by_contra! no
          simp [no] at hk
          rw [hk] at prime_p
          absurd prime_p
          norm_num
        have o: 2 ≤ m := by omega
        use 5 * m + 2
        use 18
        simp
        constructor
        . simp [hk]
          have o: 2 ≤ k := by omega
          qify at o
          nlinarith
        . constructor
          . by_contra! no
            rw [hk] at no
            rw [Nat.cast_add] at no
            absurd no
            simp
            qify at o
            nlinarith
          . constructor
            . ring_nf
              rw [show 36 + m * 90 - 1 = 5 * (18 * m + 7) by omega]
              rw [← hk]
              apply Nat.dvd_mul_left
            . omega

      -- case: p % 9 = 8
      . replace mod9: 9 ∣ p - 8 := by omega
        have mod9':= mod9
        apply exists_eq_mul_right_of_dvd at mod9
        obtain ⟨k,hk⟩ := mod9
        replace hk: p = 9 * k + 8 := by omega
        use k + 1
        use 9
        simp
        have ne1: p ≠ 18 := by
              by_contra! no
              rw [no] at prime_p
              absurd prime_p
              norm_num
        have ne2: p ≠ 17 := by
              by_contra! no
              absurd h
              simp [no]
              use 3
              simp
              use 6
              simp
              norm_num
        replace l: 18 < p := by omega
        constructor
        . simp [hk]
          have o: 1 ≤ k := by omega
          qify at o
          nlinarith
        . constructor
          . qify at l
            nlinarith
          . constructor
            . ring_nf
              rw [show 9 + k * 9 - 1 = 9 * k + 8 by omega]
              rw [← hk]
            . omega
  -- Then we enumerate the primes less than 16
    rcases h with ⟨h1,h2⟩
    interval_cases p
    all_goals try omega
    all_goals absurd h1; norm_num
    -- we're left to check p = 11
    absurd h2
    use 3
    use 4
    norm_num

  -- the backward direction
  . intro h
    simp at h
    rcases h with hp | hp | hp | hp | hp
    -- p = 2
    . rw [hp]
      constructor
      . norm_num
      . by_contra! h
        obtain ⟨a,b,ha,hb,h1,h2,h3,h4⟩ := h
        simp at h1 h2
        linarith
    -- p = 3
    . rw [hp]
      constructor
      . norm_num
      . by_contra! h
        obtain ⟨a,b,ha,hb,h1,h2,h3,h4⟩ := h
        replace h1: ↑a < (2: ℚ) := by linarith
        replace h2: ↑b < (2: ℚ) := by linarith
        simp at h1 h2
        absurd h4
        simp
        nlinarith
    -- p = 5
    . rw [hp]
      constructor
      . norm_num
      . by_contra! h
        obtain ⟨a,b,ha,hb,h1,h2,h3,h4⟩ := h
        replace h1: ↑a < (3: ℚ) := by linarith
        replace h2: ↑b < (3: ℚ) := by linarith
        simp at h1 h2
        replace h1: a ≤ 2 := by omega
        replace h2: b ≤ 2 := by omega
        apply Nat.le_of_dvd at h3
        absurd h3
        simp
        have o: a * b ≤ 4 := by nlinarith
        replace o: a * b - 1 ≤ 3 := by omega
        linarith
        linarith
    -- p = 7
    . rw [hp]
      constructor
      . norm_num
      . by_contra! h
        obtain ⟨a,b,ha,hb,h1,h2,h3,h4⟩ := h
        replace h1: ↑a < (4: ℚ) := by linarith
        replace h2: ↑b < (4: ℚ) := by linarith
        simp at h1 h2
        replace h1: a ≤ 3 := by omega
        replace h2: b ≤ 3 := by omega
        have h3':= h3
        apply Nat.le_of_dvd at h3
        absurd h3
        simp
        have a_val: a = 3 := by
          by_contra! no
          replace no: a ≤ 2 := by omega
          have o: a * b ≤ 6 := by nlinarith
          replace o: a * b - 1 ≤ 5 := by omega
          linarith
        have b_val: b = 3 := by
          by_contra! no
          replace no: b ≤ 2 := by omega
          have o: a * b ≤ 6 := by nlinarith
          replace o: a * b - 1 ≤ 5 := by omega
          linarith
        simp [a_val,b_val] at h3'
        omega
        omega
    -- p = 13
    . rw [hp]
      constructor
      . norm_num
      . by_contra! h
        obtain ⟨a,b,ha,hb,h1,h2,h3,h4⟩ := h
        replace h1: ↑a < (7: ℚ) := by linarith
        replace h2: ↑b < (7: ℚ) := by linarith
        simp at h1 h2
        replace h1: a ≤ 6 := by omega
        replace h2: b ≤ 6 := by omega
        interval_cases a <;> interval_cases b <;> omega
