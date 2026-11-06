import Mathlib

/-What is the least positive whole number divisible by four different prime numbers?-/

theorem algebra_12792: IsLeast {n: ℕ | 0 < n ∧ ∃ p q r s, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ Nat.Prime s ∧
  p < q ∧ q < r ∧ r < s ∧ p ∣ n ∧  q ∣ n ∧  r ∣ n ∧ s ∣ n} 210 := by

  constructor
  -- show 210 is in the set
  .
    simp
    use 2
    norm_num
    use 3
    norm_num
    use 5
    norm_num
    use 7
    norm_num

  -- show that 210 is the least element
  .
    intro n h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨hn, p, q, r, s, hp, hq, hr, hs, l1, l2, l3, d1, d2, d3, d4⟩ := h
    have lp: 2 ≤ p := by
      by_contra! o
      interval_cases p
      all_goals norm_num at hp
    have lq: 3 ≤ q := by
      by_contra! o
      interval_cases q
      all_goals norm_num at hq
      linarith
    have lr: 5 ≤ r := by
      by_contra! o
      interval_cases r
      all_goals norm_num at hr
      all_goals linarith
    have ls: 7 ≤ s := by
      by_contra! o
      interval_cases s
      all_goals norm_num at hs
      all_goals linarith
    have r1: 6 ≤ p * q := by nlinarith
    have r2: 30 ≤ p * q * r := by nlinarith
    have r3: 210 ≤ p * q * r * s := by nlinarith
    have d: p * q * r * s ∣ n := by  -- since they are coprime
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      apply Nat.Coprime.mul
      apply Nat.Coprime.mul
      .
        rw [Nat.Prime.coprime_iff_not_dvd]
        by_contra! o
        rw [Nat.prime_dvd_prime_iff_eq] at o
        linarith
        exact hp
        exact hs
        exact hp
      .
        rw [Nat.Prime.coprime_iff_not_dvd]
        by_contra! o
        rw [Nat.prime_dvd_prime_iff_eq] at o
        linarith
        exact hq
        exact hs
        exact hq
      .
        rw [Nat.Prime.coprime_iff_not_dvd]
        by_contra! o
        rw [Nat.prime_dvd_prime_iff_eq] at o
        linarith
        exact hr
        exact hs
        exact hr
      .
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        apply Nat.Coprime.mul
        rw [Nat.Prime.coprime_iff_not_dvd]
        by_contra! o
        rw [Nat.prime_dvd_prime_iff_eq] at o
        linarith
        exact hp
        exact hr
        exact hp
        .
          rw [Nat.Prime.coprime_iff_not_dvd]
          by_contra! o
          rw [Nat.prime_dvd_prime_iff_eq] at o
          linarith
          exact hq
          exact hr
          exact hq
        .
          apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
          rw [Nat.Prime.coprime_iff_not_dvd]
          by_contra! o
          rw [Nat.prime_dvd_prime_iff_eq] at o
          linarith
          exact hp
          exact hq
          exact hp
          exact d1
          exact d2
        exact d3
      exact d4

    -- then we can use division to show the bound
    apply Nat.le_of_dvd at d
    linarith
    exact hn
    