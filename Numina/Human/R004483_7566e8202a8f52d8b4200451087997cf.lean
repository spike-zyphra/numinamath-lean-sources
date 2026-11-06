import Mathlib

/- A positive integer $n$ cannot be divisible by 2 or 3,
 and there do not exist non-negative integers $a, b$, such that $\left|2^{a}-3^{b}\right|=n$. Find the minimum value of $n$. -/

theorem number_theory_272985: IsLeast {n: ℤ | 0 < n ∧ ¬ 2 ∣ n ∧ ¬ 3 ∣ n ∧ ∀ a b : ℕ, |(2 ^ a : ℤ) - 3 ^ b| ≠ n} 35 := by

  constructor 

  -- show that 35 is achievable
  .
    simp
    norm_num
    intro a b
    by_contra! h
    apply eq_or_eq_neg_of_abs_eq at h
    rcases h with h | h

    -- case 1
    .
      have la: 3 ≤ a := by
        suffices 2 ^ 3 ≤ 2 ^ a by
          rw [pow_le_pow_iff_right₀] at this
          tauto
          norm_num
        suffices 0 ≤ (3: ℤ) ^ b by linarith
        apply pow_nonneg
        norm_num

      -- mod 8 to derive contradiction
      replace h: ((2: ℤ) ^ a - 3 ^ b) % 8 = 35 % 8 := by
        rw [h]
      rw [Int.sub_emod] at h
      have u: 2 ^ a % 8 = 0 := by
        rw [show a = a - 3 + 3 by omega]
        ring_nf
        rw [Nat.mul_mod]
        simp
      zify at u
      rw [u] at h
      simp at h
      by_cases s: Odd b

      -- case b is odd
      .
        apply Odd.exists_bit1 at s
        obtain ⟨k, hk⟩ := s
        have v: 3 ^ b % (8: ℤ) = 3 := by
          simp [hk]
          ring_nf
          rw [Int.mul_emod]
          suffices 3 ^ (k * 2) % 8 = 1 by
            zify at this
            simp [this]
          rw [show k * 2 = 2 * k by ring]
          rw [show 3 ^ (2 * k) = (3 ^ 2) ^ k by rw [pow_mul]]
          simp
          rw [Nat.pow_mod]
          simp
        simp [v] at h
      .
        -- case b is even
        simp at s
        rw [even_iff_exists_two_mul] at s
        obtain ⟨k, hk⟩ := s
        have v: 3 ^ b % (8: ℤ) = 1 := by
          simp [hk]
          ring_nf
          rw [show k * 2 = 2 * k by ring]
          suffices  3 ^ (2 * k) % 8 = 1 by
            zify at this
            tauto
          rw [show 3 ^ (2 * k) = (3 ^ 2) ^ k by rw [pow_mul]]
          simp
          rw [Nat.pow_mod]
          simp
        simp [v] at h

    -- case 2
    .
      have lb: 3 ≤ b := by
        suffices 3 ^ 3 ≤ 3 ^ b by
          rw [pow_le_pow_iff_right₀] at this
          tauto
          norm_num
        suffices 0 ≤ (2: ℤ) ^ a by linarith
        apply pow_nonneg
        norm_num

      -- then we show that 6 ∣ a by mod 9
      have da: 6 ∣ a := by
        replace h: (2 ^ a - 3 ^ b) % 9 = (-35: ℤ) % 9 := by
          rw [h]
        rw [Int.sub_emod] at h
        have u: 3 ^ b % (9: ℤ) = 0 := by
          rw [show b = b - 2 + 2 by omega]
          ring_nf
          rw [Int.mul_emod]
          simp
        simp [u] at h
        set p:= a / 6
        set q:= a % 6
        have o: a = 6 * p + q := by
          simp [p, q]
          omega
        suffices q = 0 by omega
        by_contra! s
        have l: 1 ≤ q := by omega
        have r: q ≤ 5 := by omega
        replace h: 2 ^ a % 9 = 1 := by
          zify
          tauto
        simp [o] at h
        ring_nf at h
        have v: 2 ^ (p * 6) % 9 = 1 := by
          rw [show p * 6 = 6 * p by ring]
          rw [pow_mul]
          simp
          rw [Nat.pow_mod]
          simp
        rw [Nat.mul_mod] at h
        simp [v] at h
        clear *- l r h
        interval_cases q <;> norm_num at h

      apply exists_eq_mul_right_of_dvd at da
      obtain ⟨k, hk⟩ := da

      -- then we show that 6 ∣ b by mod 7
      have db: 6 ∣ b := by
        have o: 2 ^ a = 8 ^ (2 * k) := by
          rw [hk]
          rw [pow_mul]
          rw [pow_mul]
          simp
        zify at o
        rw [o] at h
        clear o
        replace h: (8 ^ (2 * k) - 3 ^ b) % 7 = (-35: ℤ) % 7 := by
          rw [h]
        rw [Int.sub_emod] at h
        have u: 8 ^ (2 * k) % 7 = 1 := by
          rw [Nat.pow_mod]
          simp
        zify at u
        simp [u] at h
        set p:= b / 6
        set q:= b % 6
        have o: b = 6 * p + q := by
          simp [p, q]
          omega
        suffices q = 0 by omega
        by_contra! s
        have l: 1 ≤ q := by omega
        have r: q ≤ 5 := by omega

        replace h: 3 ^ b % 7 = 1 := by
          zify
          rw [Int.dvd_iff_emod_eq_zero] at h
          set r:= (3: ℤ) ^ b
          clear *- h
          clear_value r
          omega
        simp [o] at h
        ring_nf at h
        have v: 3 ^ (p * 6) % 7 = 1 := by
          rw [show p * 6 = 6 * p by ring]
          rw [pow_mul]
          simp
          rw [Nat.pow_mod]
          simp
        rw [Nat.mul_mod] at h
        simp [v] at h
        clear *- l r h
        interval_cases q <;> norm_num at h

      apply exists_eq_mul_right_of_dvd at db
      obtain ⟨k', hk'⟩ := db
      replace h: 3 ^ b - 2 ^ a = (35: ℤ) := by
        clear *- h
        omega
      rw [hk, hk'] at h
      set i:= (3: ℤ) ^ (3 * k')
      set j:= (2: ℤ) ^ (3 * k)
      have v: (3: ℤ) ^ (6 * k') - 2 ^ (6 * k) = (i - j) * (i + j) := by
        have f: 3 ^ (6 * k') = i ^ 2 := by
          simp [i]
          ring
        have g: 2 ^ (6 * k) = j ^ 2 := by
          simp [j]
          ring
        simp [f, g]
        clear_value i j
        ring
      rw [v] at h
      clear v
      have s1: 0 ≤ i := by
        simp [i]
      have s2: 0 ≤ j := by
        simp [j]
      have y: |i + j| = i + j := by
        apply abs_of_nonneg
        omega
      have t: (i + j).natAbs ∈ Nat.divisors 35 := by
        simp
        zify
        rw [← h]
        rw [y]
        simp
      rw [show Nat.divisors 35 = {1, 5, 7, 35} by native_decide] at t
      simp at t
      zify at t
      simp [y] at t
      clear y

      -- then we must have i - j = 1 in fact
      rcases t with t | t | t | t
      .
        simp [t] at h
        clear *- s1 s2 t h
        clear_value i j
        omega
      .
        simp [t] at h
        clear *- s1 s2 t h
        clear_value i j
        omega
      .
        simp [t] at h
        replace h: i - j = 5 := by
          clear *- h
          omega
        have ei: i = 6 := by omega
        simp [i] at ei
        have x: 2 = 3 := by
          zify
          have r1: 2 ∣ 3 ^ (3 * k') := by
            zify
            rw [ei]
            norm_num
          apply Nat.prime_eq_prime_of_dvd_pow at r1
          tauto
          norm_num
          norm_num
        norm_num at x
      .
        simp [t] at h
        have ei: i = 18 := by omega
        simp [i] at ei
        have x: 2 = 3 := by
          zify
          have r1: 2 ∣ 3 ^ (3 * k') := by
            zify
            rw [ei]
            norm_num
          apply Nat.prime_eq_prime_of_dvd_pow at r1
          tauto
          norm_num
          norm_num
        norm_num at x


  -- show that any n less than 35 is impossible, we need to check one by one
  .
    intro n h
    rw [Set.mem_setOf] at h
    by_contra! l
    rcases h with ⟨h1, h2, h3, h⟩
    interval_cases n <;> norm_num at h2 <;> norm_num at h3
    all_goals absurd h; simp

    -- n = 1
    . use 1, 1; norm_num

    -- n = 5
    . use 3, 1; norm_num

    -- n = 7
    . use 4, 2; norm_num

    -- n = 11
    . use 4, 3; norm_num

    -- n = 13
    . use 4, 1; norm_num

    -- n = 17
    . use 6, 4; norm_num

    -- n = 19
    . use 3, 3; norm_num

    -- n = 23
    . use 5, 2; norm_num

    -- n = 25
    . use 1, 3; norm_num

    -- n = 29
    . use 5, 1; norm_num

    -- n = 31
    . use 5, 0; norm_num