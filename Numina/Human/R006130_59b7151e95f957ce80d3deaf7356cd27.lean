import Mathlib

/-
Determine all solutions $(m, n) \in \mathbb{N}^2$ to the Diophantine equation $2^m = 5 \cdot 3^n + 1$. -/

theorem number_theory_619229: {(m, n): ℕ × ℕ | 2^m = 5 * 3^n + 1} = {(4, 1)} := by

  ext ⟨m, n⟩
  constructor
  -- the forward direction
  .
    intro h
    simp at *
    by_cases ln: n = 0
    -- case n = 0
    .
      simp [ln] at h
      have l1: 2 < m := by
        by_contra! o
        have s: 6 ≤ 4 := by
          rw [← h]
          rw [show 4 = 2^2 by rfl]
          apply Nat.pow_le_pow_right
          norm_num
          exact o
        tauto
      have l2: m < 3 := by
        by_contra! o
        have s: 8 ≤ 6 := by
          rw [← h]
          rw [show 8 = 2^3 by rfl]
          apply Nat.pow_le_pow_right
          norm_num
          exact o
        tauto
      omega
    -- case n > 0
    .
      replace ln: 1 ≤ n := by omega

      -- then we show that 4 ≤ m
      have lm: 4 ≤ m := by
        have o: 2 ^ 4 ≤ 5 * 3 ^ n + 1 := by
          have s: 3 ≤ 3 ^ n := by
            rw [show 3 = 3^1 by rfl]
            apply Nat.pow_le_pow_right
            norm_num
            exact ln
          omega
        rw [← h] at o
        rw [Nat.pow_le_pow_iff_right] at o
        exact o
        norm_num

      -- next we show that m is even
      have em: Even m := by
        by_contra! o
        simp at o
        have p: 2 ^ m % 3 = 1 := by
          rw [h]
          rw [Nat.add_mod]
          have o1: 1 % 3 = 1 := by
            norm_num
          rw [o1]
          have o2: 5 * 3 ^ n % 3 = 0 := by
            apply Nat.mod_eq_zero_of_dvd
            have eq: 5 * 3 ^ n = 3 * (5 * 3 ^ (n - 1)) := by
              have e: 3 ^ n = 3 * 3 ^ (n - 1) := by
                rw [← mul_pow_sub_one]
                omega
              rw [e]
              ring
            rw [eq]
            simp
          rw [o2]
        apply Odd.exists_bit1 at o
        obtain ⟨k, hk⟩:= o
        simp [hk] at p
        have eq: 2 ^ (2 * k + 1) = 4 ^ k * 2 := by
          rw [Nat.pow_add_one]
          rw [Nat.pow_mul]
        rw [eq] at p
        rw [Nat.mul_mod] at p
        rw [Nat.pow_mod] at p
        norm_num at p

      -- then we use m is even to factor
      rw [even_iff_exists_two_mul] at em
      obtain ⟨k, hk⟩:= em
      rw [hk] at h
      replace h: 2 ^ (2 * k) - 1 = 5 * 3 ^ n := by
        rw [h]
        omega
      have eq: 2 ^ (2 * k) =  (2 ^ k) ^ 2 := by
        rw [show 2 * k = k * 2 by ring]
        rw [Nat.pow_mul]
      rw [eq] at h
      clear eq
      have eq:  (2 ^ k) ^ 2 - 1 = (2 ^ k - 1) * (2 ^ k + 1) := by
        have o: 1 ≤ 2 ^ k := by
          apply Nat.one_le_two_pow
        set a:= 2 ^ k
        have s: 1 ≤ a ^ 2 := by
          apply Nat.one_le_pow
          exact o
        zify
        rw [show ↑(a - 1) = (a: ℤ) - (1: ℤ) by apply Int.natCast_sub; omega]
        have eq: ↑(a ^ 2 - (1: ℕ)) = ↑(a ^ 2) - (1: ℤ) := by
          apply Int.natCast_sub
          exact s
        rw [eq]
        have r: ↑(a ^ 2) = (a: ℤ) ^ 2 := by
          rw [Int.natCast_pow]
        rw [r]
        ring
      rw [eq] at h
      clear eq
      set p:= 2 ^ k - 1 with hp
      set q:= 2 ^ k + 1 with hq

      -- then we show that p and q are coprime, so that one is 3 ^ n, another is 5
      have pp: Nat.Coprime p q := by   -- show that they are coprime
        have i: q = p + 2 := by
          rw [hq]
          rw [hp]
          have o: 1 ≤ 2 ^ k := by
            apply Nat.one_le_two_pow
          rw [show 2 ^ k - 1 + 2 = (2 ^ k - 1 + 1) + 1 by ring]
          rw [show 2 ^ k - 1 + 1 = 2 ^ k by omega]
        have j: Odd p := by
          simp [hp]
          apply Nat.Even.sub_odd
          apply Nat.one_le_two_pow
          rw [Nat.even_pow']
          norm_num
          by_contra! o
          simp [o] at hk
          simp [hk] at lm
          decide
        rw [i]
        clear * - j
        clear_value p
        apply Nat.Coprime.symm
        rw [← Nat.coprime_self_sub_right]
        rw [show p + 2 - p = 2 by omega]
        apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd]
        by_contra! i
        replace i: 2 ∣ p := by
          rw [show p = p + 2 - 2 by omega]
          apply Nat.dvd_sub
          omega
          exact i
          omega
        rw [← even_iff_two_dvd] at i
        absurd j
        simp at j
        simp
        exact i
        norm_num
        omega
      have d: 3 ^ n ∣ p * q := by
        rw [h]
        rw [show 5 * 3 ^ n = 5 * (3 ^ n) by rfl]
        simp
      have g: IsPrimePow (3 ^ n) := by
        rw [isPrimePow_nat_iff]
        use 3
        use n
        norm_num
        omega
      rw [Nat.Coprime.isPrimePow_dvd_mul pp g] at d
      rcases d with d | d
      .
        --case: p = 3 ^ n, q = 5
        apply exists_eq_mul_right_of_dvd at d
        obtain ⟨u, hu⟩:= d
        simp [hu] at h
        rw [show 3 ^ n * u * q = (u * q) * 3 ^ n by ring] at h
        apply Nat.mul_right_cancel at h
        have lq: q ≤ 5 := by
          rw [← h]
          have lu: 1 ≤ u := by
            by_contra! o
            replace o: u = 0 := by omega
            simp [o] at h
          nlinarith
        simp [hq] at lq
        rw [show 4 = 2 ^ 2 by rfl] at lq
        rw [Nat.pow_le_pow_iff_right] at lq
        interval_cases k
        .
          simp at hp hq hk
          simp [hk] at lm
        .
          simp [hk] at lm
        .
          simp at hk
          simp [hk]
          simp [hp] at hu
          simp [hq] at h
          simp [h] at hu
          symm at hu
          rw [Nat.pow_eq_self_iff] at hu
          exact hu
          norm_num
        norm_num
        apply Nat.pow_pos
        norm_num
      .
        --case: p = 5, q = 3 ^ n
        apply exists_eq_mul_left_of_dvd at d
        obtain ⟨u, hu⟩:= d
        simp [hu] at h
        rw [show p * (u * 3 ^ n) = p * u * 3 ^ n by ring] at h
        apply Nat.mul_right_cancel at h
        have lp: p ≤ 5 := by
          rw [← h]
          have lu: 1 ≤ u := by
            by_contra! o
            replace o: u = 0 := by omega
            simp [o] at h
          nlinarith
        simp [hp] at lp
        replace lp: 2 ^ k < 2 ^ 3 := by
          linarith
        rw [Nat.pow_lt_pow_iff_right] at lp
        interval_cases k
        .
          simp at hp hq hk
          simp [hk] at lm
        .
          simp [hk] at lm
        .
          simp at hk
          simp [hk]
          simp at hp hq
          simp [hp,hq] at hu h
          omega
        norm_num
        apply Nat.pow_pos
        norm_num

  -- the backward direction
  .
    intro h
    simp at *
    simp [h]