import Mathlib

open Finset Real Nat

-- we show a lemma to split the sum of factorials into two parts
lemma sum_splits (a b c: ℕ) (h1: a ≤ b) (h2: b ≤ c):
  ∑ i ∈ Icc a c, Nat.factorial i = (∑ i ∈ Icc a b, Nat.factorial i) + (∑ i ∈ Icc (b + 1) c, Nat.factorial i) := by

    -- show the union of the two parts is the same as the whole
    have s1: Icc a c = Icc a b ∪ Icc (b + 1) c := by
      ext i
      constructor
      .
        intro h
        simp at h
        simp
        by_cases l: i ≤ b
        .
          left
          omega
        .
          right
          omega
      .
        intro h
        simp at h
        rcases h with h | h
        .
          simp
          omega
        .
          simp
          omega

    -- show the two parts are disjoint
    have s2: Disjoint (Icc a b) (Icc (b + 1) c) := by
      intro x h1 h2
      simp at h1 h2
      simp
      ext y
      simp
      by_contra! h
      have l1: y ∈ Icc a b := by
        exact Set.mem_of_mem_of_subset h h1
      have l2: y ∈ Icc (b + 1) c := by
        exact Set.mem_of_mem_of_subset h h2
      simp at l1 l2
      omega

    -- use the above facts
    rw [s1]
    clear s1
    rw [Finset.sum_union]
    exact s2

-- we show all possible values of n ^ 2 mod 5
lemma sq_mod_5 (n: ℕ): n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by
  rw [Nat.pow_mod]
  set b:= n % 5
  have o: b < 5 := by omega
  clear_value b
  interval_cases b
  all_goals simp


/-Find the integers m, n, k greater than 1 such that
1! + 2! +... + m! = n ^ k-/

theorem number_theory_310562: {(m, n, k): ℕ × ℕ × ℕ | 1 < m ∧ 1 < n ∧ 1 < k ∧ ∑ i ∈ Icc 1 m, Nat.factorial i = n ^ k}
  = {(3, 3, 2)} := by

    ext ⟨m, n, k⟩
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      rcases h with ⟨hm, hn, hk, h⟩
      simp
      by_cases l: m < 8

      -- we first tackle the case m < 8 one by one
      .
        have r: n ^ 2 ≤ n ^ k := by
          apply Nat.pow_le_pow_of_le_right
          omega
          omega
        interval_cases m

        -- m = 2
        .
          simp [Finset.sum_Icc_succ_top] at h
          have d: n ∣ 3 := by
            rw [show n = n ^ 1 by simp]
            rw [h]
            apply Nat.pow_dvd_pow
            omega
          apply Nat.le_of_dvd at d
          interval_cases n
          .
            have o: 2 ∣ 3 := by
              rw [show 2 = 2 ^ 1 by simp]
              rw [h]
              apply Nat.pow_dvd_pow
              omega
            norm_num at o
          .
            symm at h
            rw [Nat.pow_eq_self_iff ] at h
            simp [h] at hk
            norm_num
          norm_num

        -- m = 3
        .
          simp [Finset.sum_Icc_succ_top] at h
          rw [show 3 + 3! = 9 by decide] at h
          rw [← h] at r
          have ln: n ≤ 3:= by nlinarith
          interval_cases n
          .
            have o: 2 ∣ 9 := by
              rw [show 2 = 2 ^ 1 by simp]
              rw [h]
              apply Nat.pow_dvd_pow
              omega
            norm_num at o
          .
            rw [show 9 = 3 ^ 2 by decide] at h
            rw [pow_right_inj₀] at h
            simp [h]
            norm_num
            norm_num

        -- m = 4
        .
          simp [Finset.sum_Icc_succ_top] at h
          rw [show 3 + 3! + 4! = 33 by decide] at h
          rw [← h] at r
          have ln: n ≤ 5 := by nlinarith
          have dn: 11 ∣ n := by
            have o: 11 ∣ n ^ k := by
              rw [← h]
              norm_num
            apply Nat.Prime.dvd_of_dvd_pow at o
            exact o
            norm_num
          apply Nat.le_of_dvd at dn
          linarith
          linarith

        -- m = 5
        .
          simp [Finset.sum_Icc_succ_top] at h
          rw [show 3 + 3! + 4! + 5! = 153 by decide] at h
          rw [← h] at r
          have ln: n ≤ 12 := by nlinarith
          have dn: 17 ∣ n := by
            have o: 17 ∣ n ^ k := by
              rw [← h]
              norm_num
            apply Nat.Prime.dvd_of_dvd_pow at o
            exact o
            norm_num
          apply Nat.le_of_dvd at dn
          linarith
          linarith

        -- m = 6
        .
          simp [Finset.sum_Icc_succ_top] at h
          rw [show 3 + 3! + 4! + 5! + 6! = 873 by decide] at h
          rw [← h] at r
          have ln: n ≤ 29 := by nlinarith
          have dn: 97 ∣ n := by
            have o: 97 ∣ n ^ k := by
              rw [← h]
              norm_num
            apply Nat.Prime.dvd_of_dvd_pow at o
            exact o
            norm_num
          apply Nat.le_of_dvd at dn
          linarith
          linarith

        -- m = 7
        .
          simp [Finset.sum_Icc_succ_top] at h
          rw [show 3 + 3! + 4! + 5! + 6! + 7! = 5913 by decide] at h
          rw [← h] at r
          have ln: n ≤ 77 := by nlinarith
          have dn: 73 ∣ n := by
            have o: 73 ∣ n ^ k := by
              rw [← h]
              norm_num
            apply Nat.Prime.dvd_of_dvd_pow at o
            exact o
            norm_num
          apply exists_eq_mul_right_of_dvd at dn
          obtain ⟨t, ht⟩ := dn
          have lt: t = 1 := by omega
          simp [lt] at ht
          simp [ht] at h
          have o: 3 ∣ 73 := by
            have o: 3 ∣ 5913 := by norm_num
            rw [h] at o
            apply Nat.Prime.dvd_of_dvd_pow at o
            exact o
            norm_num
          norm_num at o


      -- then we show that there are no solutions for 8 ≤ m
      .
        simp at l

        -- we first show that k = 2
        have vk: k = 2 := by
          by_contra! lk
          replace lk: 3 ≤ k := by omega
          have eq: ∑ i ∈ Icc 1 m, Nat.factorial i =
            (∑ i ∈ Icc 1 8, Nat.factorial i) + (∑ i ∈ Icc 9 m, Nat.factorial i) := by
            exact sum_splits 1 8 m (by omega) (by omega)
          have o: ∑ i ∈ Icc 1 8, Nat.factorial i = 46233 := by
            simp [Finset.sum_Icc_succ_top]
            decide
          rw [o] at eq
          clear o

          -- then we show contradiction by noting that the pow of 3 is exactly 2 of right side
          have f: 27 ∣ ∑ i ∈ Icc 9 m, Nat.factorial i := by
            apply Finset.dvd_sum
            intro i hi
            simp at hi
            have g: 27 ∣ 9! := by
              rw [show 9! = 362880 by decide]
              norm_num
            have g2: 9! ∣ Nat.factorial i := by
              apply Nat.factorial_dvd_factorial
              omega
            apply dvd_trans g g2
          rw [h] at eq
          clear h
          have f2: 3 ∣ n ^ k := by
            rw [eq]
            apply Nat.dvd_add
            .
              norm_num
            .
              have o: 3 ∣ 27 := by norm_num
              apply dvd_trans o f
          apply Nat.Prime.dvd_of_dvd_pow at f2
          replace f2: 27 ∣ n ^ k := by
            have o: 27 ∣ n ^ 3 := by
              rw [show 27 = 3 ^ 3 by simp]
              rw [Nat.pow_dvd_pow_iff]
              exact f2
              norm_num
            have o2: n ^ 3 ∣ n ^ k := by
              apply Nat.pow_dvd_pow
              omega
            apply dvd_trans o o2
          rw [eq] at f2
          have c: 27 ∣ 46233 := by
            rw [show 46233 = 46233 + ∑ i ∈ Icc 9 m, Nat.factorial i - ∑ i ∈ Icc 9 m, Nat.factorial i by omega]
            apply Nat.dvd_sub
            omega
            exact f2
            exact f
          norm_num at c
          norm_num


        -- then we prove contradiction for the case k = 2 by mod 5
        .
          simp [vk] at *
          clear hk vk

          -- we show that n ^ 2 % 5 = 3 by rw [← h]
          have o: n ^ 2 % 5 = 3 := by
            rw [← h]
            clear h hn
            rw [sum_splits 1 4 m (by omega) (by omega)]
            rw [show 4 + 1 = 5 by simp]
            rw [show ∑ i ∈ Icc 1 4, Nat.factorial i = 33 by decide]
            rw [Nat.add_mod]
            rw [show 33 % 5 = 3 by decide]
            have r: (∑ i ∈ Icc 5 m, Nat.factorial i) % 5 = 0 := by
              apply Nat.mod_eq_zero_of_dvd
              apply Finset.dvd_sum
              intro i hi
              simp at hi
              apply Nat.dvd_factorial
              norm_num
              omega
            simp [r]

          -- then we use sq_mod_5 to see that "o" is impossible
          have c:= sq_mod_5 n
          simp [o] at c


    -- the backward direction
    .
      intro h
      simp at h
      simp [h]
      simp [Finset.sum_Icc_succ_top]
      decide