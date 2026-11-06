import Mathlib

/-Let a b c d e be nonnegative integers such that
625 * a + 250 * b + 100 * c + 40 * d + 16 * e = 15^3
What is the maximum possible value of a + b + c + d + e ?  -/

theorem number_theory_609359:
  IsGreatest {k : ℕ | ∃ a b c d e : ℕ, 625 * a + 250 * b + 100 * c + 40 * d + 16 * e = 15 ^ 3 ∧
   a + b + c + d + e = k} 153 := by

   constructor

   -- show 153 is in the set
   .
    simp
    use 1
    use 1
    use 1
    use 0
    use 150

   -- show 153 is the maximum
   .
    intro k hk
    obtain ⟨a, b, c, d, e, h, h2⟩ := hk
    rw [← h2]
    clear h2

    -- we prove by contradiction
    by_contra! l
    replace l: 154 ≤ a + b + c + d + e := by
      omega

    -- we show that a ≤ 2, then a must be 1 by mod2
    have ha: a = 1 := by
      have la: a < 3 := by
        by_contra! o
        have sa: a ≤ 7 := by nlinarith
        -- if 3 ≤ a, then there b, c, d, e can't be too large
        nlinarith
      have da: ¬ 2 ∣ a := by
        by_contra! da
        have r: 2 ∣ 15 ^ 3 := by
          rw [← h]
          rw [show 625 * a + 250 * b + 100 * c + 40 * d + 16 * e
          = 625 * a + 2 * (125 * b + 50 * c + 20 * d + 8 * e) by ring]
          apply Nat.dvd_add
          have o: a ∣ 625 * a := by simp
          apply dvd_trans da o
          simp
        norm_num at r
      clear * - la da
      interval_cases a
      .
        omega
      .
        omega
      .
        omega

    simp [ha] at *
    clear ha
    replace h: 250 * b + 100 * c + 40 * d + 16 * e = 2750 := by omega
    replace h: 125 * b + 50 * c + 20 * d + 8 * e = 1375 := by omega
    replace l: 153 ≤ b + c + d + e := by
      omega

    -- similarly, we have b = 1
    have hb: b = 1 := by
      have lb: b < 3 := by
        by_contra! o
        have sb: b ≤ 7 := by nlinarith
        -- if 3 ≤ b, then there c, d, e can't be too large
        nlinarith
      have db: ¬ 2 ∣ b := by
        by_contra! db
        have r: 2 ∣ 1375 := by
          rw [← h]
          rw [show 125 * b + 50 * c + 20 * d + 8 * e
          = 125 * b + 2 * (25 * c + 10 * d + 4 * e) by ring]
          apply Nat.dvd_add
          have o: b ∣ 125 * b := by simp
          apply dvd_trans db o
          simp
        norm_num at r
      clear * - lb db
      interval_cases b
      .
        omega
      .
        omega
      .
        omega

    simp [hb] at *
    clear hb
    replace h: 50 * c + 20 * d + 8 * e = 1250 := by omega
    replace h: 25 * c + 10 * d + 4 * e = 615 := by omega
    replace l: 152 ≤ c + d + e := by
      omega

    -- similarly, we have c = 1
    have hc: c = 1 := by
      have lc: c < 3 := by
        by_contra! o
        have sc: c ≤ 7 := by nlinarith
        -- if 3 ≤ c, then there d, e can't be too large
        nlinarith
      have dc: ¬ 2 ∣ c := by
        by_contra! dc
        have r: 2 ∣ 615 := by
          rw [← h]
          rw [show 25 * c + 10 * d + 4 * e
          = 25 * c + 2 * (5 * d + 2 * e) by ring]
          apply Nat.dvd_add
          have o: c ∣ 25 * c := by simp
          apply dvd_trans dc o
          simp
        norm_num at r
      clear * - lc dc
      interval_cases c
      .
        omega
      .
        omega
      .
        omega

    -- finally, we're left with d and e
    simp [hc] at *
    clear hc
    replace h: 10 * d + 4 * e = 590 := by omega
    replace l: 151 ≤ d + e := by
      omega

    -- note that now 590 ≥ 4 * (d + e) > 600, so there is no solution
    nlinarith
    