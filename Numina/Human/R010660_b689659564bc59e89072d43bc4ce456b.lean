import Mathlib

open Finset Real Nat
/-There are two prime numbers p so that 5p can be expressed in the form floor.n^2/5
for some positive integer n. What is the sum of these two prime numbers?-/
theorem number_theory_609784 (p: ℤ) (Prime_p:Prime p) (bp: 2 ≤ p) (hp: ∃ n: ℤ, (1 ≤ n) ∧ (5 * p = n ^ 2 / 5))
(q: ℤ) (Prime_q:Prime q) (bq: 2 ≤ q) (hq: ∃ m: ℤ, (1 ≤ m) ∧ (5 * q = m ^ 2 / 5)) (pneq: p < q): p + q = 52 := by
 -- the following three lemma will be used later --
  have mod25_1: ∀ n: ℤ, (1 ≤ n) ∧ (25 ∣ (n - 1) * (n + 1)) → (25 ∣ n - 1) ∨ (25 ∣ n + 1) := by
    intro n
    simp
    intro bn
    intro h
    by_contra! hn
    have d1: 5 ∣ n - 1 := by
      by_contra! d1
      replace h: 5 ^ 2 ∣ (n - 1) * (n + 1) := by
        simp
        exact h
      apply Prime.pow_dvd_of_dvd_mul_left at h
      omega
      norm_num
      exact d1
    have d2: 5 ∣ n + 1 := by
      by_contra! d2
      replace h: 5 ^ 2 ∣ (n + 1) * (n - 1) := by
        simp
        ring_nf at h
        ring_nf
        exact h
      apply Prime.pow_dvd_of_dvd_mul_left at h
      omega
      norm_num
      exact d2
    have d3: 5 ∣ 2 := by omega
    tauto

  have mod25_2: ∀ n: ℤ, (1 ≤ n) ∧ (25 ∣ (n - 2) * (n + 2)) → (25 ∣ n - 2) ∨ (25 ∣ n + 2) := by
    intro n
    simp
    intro bn
    intro h
    by_contra! hn
    have d1: 5 ∣ n - 2 := by
      by_contra! d1
      replace h: 5 ^ 2 ∣ (n - 2) * (n + 2) := by
        simp
        exact h
      apply Prime.pow_dvd_of_dvd_mul_left at h
      omega
      norm_num
      exact d1
    have d2: 5 ∣ n + 2 := by
      by_contra! d2
      replace h: 5 ^ 2 ∣ (n + 2) * (n - 2) := by
        simp
        ring_nf at h
        ring_nf
        exact h
      apply Prime.pow_dvd_of_dvd_mul_left at h
      omega
      norm_num
      exact d2
    have d3: 5 ∣ 4:= by omega
    tauto

  have sq_mod5: ∀ x: ℤ, (5 ∣x ^ 2) ∨ (5 ∣ x ^ 2 - 1) ∨ (5 ∣ x ^ 2 - 4) := by
    intro x
    let d := x % 5
    let q := x / 5
    have h: x = 5 * q + d := by simp [q,d]; omega
    have hd: d ∈ Icc 0 4 := by
      simp
      omega
    clear_value d
    fin_cases hd
    -- d = 0 --
    . simp at h
      simp [h]
      left
      ring_nf
      omega
    -- d = 1 --
    . simp at h
      simp [h]
      right
      left
      ring_nf
      omega
    -- d = 2 --
    . simp at h
      simp [h]
      right
      right
      ring_nf
      omega
    -- d = 3 --
    . simp at h
      simp [h]
      right
      right
      ring_nf
      omega
    -- d = 4 --
    . simp at h
      simp [h]
      right
      left
      ring_nf
      omega

-- This lemma gives all possible values of p --
  have p_val: p = 23 ∨ p = 29 := by
    obtain ⟨n, hp⟩ := hp
    let r:= n ^ 2 / 5
    let s:= n ^ 2 % 5
    have n_deup: n ^ 2 = 5 * r + s := by simp [r,s]; omega
    have sq_mod5_n:= sq_mod5
    specialize sq_mod5_n n
    have hs: (s = 0) ∨ (s = 1) ∨ (s = 4) := by simp [sq_mod5_n] at n_deup; omega
    rcases hs with hs | hs | hs
    -- s = 0 --
    . simp [hs] at n_deup
      rcases hp with ⟨bn,hp⟩
      replace hs: 5 ∣ n ^ 2 := by omega
      have h: 5 ∣ n := by
        apply Prime.dvd_of_dvd_pow at hs
        exact hs
        norm_num
      clear hs
      apply exists_eq_mul_right_of_dvd at h
      obtain ⟨k,hk⟩ := h
      simp [hk] at hp
      have k1: 1 ≤ k := by omega
      have eqk: (5 * k) ^ 2 / 5 = 5 * k ^ 2 := by
        ring_nf
        omega
      rw [eqk] at hp
      simp at hp
      have kp: p ∣ k ^ 2 := by
        rw [hp]
      apply Prime.dvd_of_dvd_pow at kp
      rw [hp] at kp
      apply Int.le_of_dvd at kp
      have k2: k ≤ 1 := by
        rw [show k ^ 2 = k * k by ring] at kp
        nth_rewrite 3[show k = k * 1 by ring] at kp
        apply Int.le_of_mul_le_mul_left at kp
        omega
      replace k2 : k = 1 := by omega
      simp [k2] at hp
      omega
      omega
      exact Prime_p
    -- s = 1 --
    . simp [hs] at *
      rcases hp with ⟨bn,hp⟩
      have eq: 25 * p = (n - 1) * (n + 1) := by
        simp [n_deup] at hp
        have eqr: (5 * r + 1) / 5 = r := by
          ring_nf
          omega
        rw [eqr] at hp
        replace hp: 25 * p = 5 * r := by omega
        replace n_deup:  5 * r = n ^ 2 - 1 := by omega
        rw [n_deup] at hp
        ring_nf
        omega
      have dvd25: 25 ∣ (n - 1) * (n + 1) := by
        omega
      have n25: 25 ∣ n - 1 ∨ 25 ∣ n + 1 := by
        specialize mod25_1 n
        apply mod25_1
        omega
        exact dvd25
      rcases n25 with n25 | n25
      -- 25 ∣ n - 1 --
      . apply exists_eq_mul_right_of_dvd at n25
        obtain ⟨k,hk⟩ := n25
        rw [hk] at eq
        rw [show 25 * k * (n + 1) = 25 * (k * (n + 1)) by ring] at eq
        rw [Int.mul_eq_mul_left_iff] at eq

        -- It's not easy to show the following --
        have k_val: k = 1 := by
          let p1:= p.natAbs
          have p_prime: Nat.Prime p1 := by
            simp [p1]
            rw [Nat.prime_iff_prime_int]
            simp [Prime_p]
            have pp: |p| = p := by
              simp
              omega
            rw [pp]
            exact Prime_p
          let k1:= k.natAbs
          have pp1: p.natAbs = p1 := by simp [p1]
          have kk1: k.natAbs = k1 := by simp [k1]
          have kp: k ∣ p := by rw [eq]; apply dvd_mul_right
          rw [←Int.natAbs_dvd_natAbs] at kp
          rw [pp1] at kp
          rw [kk1] at kp
          apply Nat.Prime.eq_one_or_self_of_dvd at kp
          replace kp: k = 1 ∨ k = p := by omega
          rcases kp with kp | kp
          . exact kp
          . rw [kp] at eq
            have no: p > p := by
              calc
                p = p * (n + 1) := by omega
                  _> p * 1 := by nlinarith
                  _ = p := by ring
            omega
          . exact p_prime

        simp [k_val] at hk eq
        have p_va: p = 27 := by omega
        rw [p_va] at Prime_p
        norm_num at Prime_p
        omega
      -- 25 ∣ n + 1 --
      . apply exists_eq_mul_right_of_dvd at n25
        obtain ⟨k,hk⟩ := n25
        rw [hk] at eq
        rw [show (n - 1) * (25 * k) = 25 * (k * (n - 1)) by ring] at eq
        rw [Int.mul_eq_mul_left_iff] at eq

        have k_val: k = 1 := by
          let p1:= p.natAbs
          have p_prime: Nat.Prime p1 := by
            simp [p1]
            rw [Nat.prime_iff_prime_int]
            simp [Prime_p]
            have pp: |p| = p := by
              simp
              omega
            rw [pp]
            exact Prime_p
          let k1:= k.natAbs
          have pp1: p.natAbs = p1 := by simp [p1]
          have kk1: k.natAbs = k1 := by simp [k1]
          have kp: k ∣ p := by rw [eq]; apply dvd_mul_right
          rw [←Int.natAbs_dvd_natAbs] at kp
          rw [pp1] at kp
          rw [kk1] at kp
          apply Nat.Prime.eq_one_or_self_of_dvd at kp
          replace kp: k = 1 ∨ k = p := by omega
          rcases kp with kp | kp
          . exact kp
          . rw [kp] at eq
            have no: p > p := by
              calc
                p = p * (n - 1) := by omega
                  _> p * 1 := by nlinarith
                  _ = p := by ring
            omega
          . exact p_prime

        simp [k_val] at hk eq
        omega
        omega
     -- s = 4--
    . simp [hs] at *
      rcases hp with ⟨bn,hp⟩
      have eq: 25 * p = (n - 2) * (n + 2) := by
        simp [n_deup] at hp
        have eqr: (5 * r + 4) / 5 = r := by
          ring_nf
          omega
        rw [eqr] at hp
        replace hp: 25 * p = 5 * r := by omega
        replace n_deup:  5 * r = n ^ 2 - 4 := by omega
        rw [n_deup] at hp
        ring_nf
        omega
      have dvd25: 25 ∣ (n - 2) * (n + 2) := by
        omega
      have n25: 25 ∣ n - 2 ∨ 25 ∣ n + 2 := by
        specialize mod25_2 n
        apply mod25_2
        omega
        exact dvd25
      rcases n25 with n25 | n25
      -- 25 ∣ n - 2 --
      . apply exists_eq_mul_right_of_dvd at n25
        obtain ⟨k,hk⟩ := n25
        rw [hk] at eq
        rw [show 25 * k * (n + 2) = 25 * (k * (n + 2)) by ring] at eq
        rw [Int.mul_eq_mul_left_iff] at eq

        have k_val: k = 1 := by
          let p1:= p.natAbs
          have p_prime: Nat.Prime p1 := by
            simp [p1]
            rw [Nat.prime_iff_prime_int]
            simp [Prime_p]
            have pp: |p| = p := by
              simp
              omega
            rw [pp]
            exact Prime_p
          let k1:= k.natAbs
          have pp1: p.natAbs = p1 := by simp [p1]
          have kk1: k.natAbs = k1 := by simp [k1]
          have kp: k ∣ p := by rw [eq]; apply dvd_mul_right
          rw [←Int.natAbs_dvd_natAbs] at kp
          rw [pp1] at kp
          rw [kk1] at kp
          apply Nat.Prime.eq_one_or_self_of_dvd at kp
          replace kp: k = 1 ∨ k = p := by omega
          rcases kp with kp | kp
          . exact kp
          . rw [kp] at eq
            have no: p > p := by
              calc
                p = p * (n + 2) := by omega
                  _> p * 1 := by nlinarith
                  _ = p := by ring
            omega
          . exact p_prime

        simp [k_val] at hk eq
        omega
        omega
      -- 25 ∣ n + 2 --
      . apply exists_eq_mul_right_of_dvd at n25
        obtain ⟨k,hk⟩ := n25
        rw [hk] at eq
        rw [show (n - 2) * (25 * k) = 25 * (k * (n - 2)) by ring] at eq
        rw [Int.mul_eq_mul_left_iff] at eq

        have k_val: k = 1 := by
          let p1:= p.natAbs
          have p_prime: Nat.Prime p1 := by
            simp [p1]
            rw [Nat.prime_iff_prime_int]
            simp [Prime_p]
            have pp: |p| = p := by
              simp
              omega
            rw [pp]
            exact Prime_p
          let k1:= k.natAbs
          have pp1: p.natAbs = p1 := by simp [p1]
          have kk1: k.natAbs = k1 := by simp [k1]
          have kp: k ∣ p := by rw [eq]; apply dvd_mul_right
          rw [←Int.natAbs_dvd_natAbs] at kp
          rw [pp1] at kp
          rw [kk1] at kp
          apply Nat.Prime.eq_one_or_self_of_dvd at kp
          replace kp: k = 1 ∨ k = p := by omega
          rcases kp with kp | kp
          . exact kp
          . rw [kp] at eq
            have no: p > p := by
              calc
                p = p * (n - 2) := by omega
                  _> p * 1 := by nlinarith
                  _ = p := by ring
            omega
          . exact p_prime

        simp [k_val] at hk eq
        have p_val: p = 21 := by omega
        rw [p_val] at Prime_p
        norm_num at Prime_p
        omega

-- By the same way, this lemma gives all possible values of q --
  have q_val: q = 23 ∨ q = 29 := by
    obtain ⟨m, hq⟩ := hq
    let r:= m ^ 2 / 5
    let s:= m ^ 2 % 5
    have n_deup: m ^ 2 = 5 * r + s := by simp [r,s]; omega
    have sq_mod5_n:= sq_mod5
    specialize sq_mod5_n m
    have hs: (s = 0) ∨ (s = 1) ∨ (s = 4) := by simp [sq_mod5_n] at n_deup; omega
    rcases hs with hs | hs | hs
    -- s = 0 --
    . simp [hs] at n_deup
      rcases hq with ⟨bn,hq⟩
      replace hs: 5 ∣ m ^ 2 := by omega
      have h: 5 ∣ m := by
        apply Prime.dvd_of_dvd_pow at hs
        exact hs
        norm_num
      clear hs
      apply exists_eq_mul_right_of_dvd at h
      obtain ⟨k,hk⟩ := h
      simp [hk] at hq
      have k1: 1 ≤ k := by omega
      have eqk: (5 * k) ^ 2 / 5 = 5 * k ^ 2 := by
        ring_nf
        omega
      rw [eqk] at hq
      simp at hq
      have kp: q ∣ k ^ 2 := by
        rw [hq]
      apply Prime.dvd_of_dvd_pow at kp
      rw [hq] at kp
      apply Int.le_of_dvd at kp
      have k2: k ≤ 1 := by
        rw [show k ^ 2 = k * k by ring] at kp
        nth_rewrite 3[show k = k * 1 by ring] at kp
        apply Int.le_of_mul_le_mul_left at kp
        omega
      replace k2 : k = 1 := by omega
      simp [k2] at hq
      omega
      omega
      exact Prime_q
    -- s = 1 --
    . simp [hs] at *
      rcases hp with ⟨bn,hp⟩
      have eq: 25 * q = (m - 1) * (m + 1) := by
        simp [n_deup] at hq
        have eqr: (5 * r + 1) / 5 = r := by
          ring_nf
          omega
        rw [eqr] at hq
        replace hq: 25 * q = 5 * r := by omega
        replace n_deup:  5 * r = m ^ 2 - 1 := by omega
        rw [n_deup] at hq
        ring_nf
        omega
      have dvd25: 25 ∣ (m - 1) * (m + 1) := by
        omega
      have n25: 25 ∣ m - 1 ∨ 25 ∣ m + 1 := by
        specialize mod25_1 m
        apply mod25_1
        omega
        exact dvd25
      rcases n25 with n25 | n25
      -- 25 ∣ n - 1 --
      . apply exists_eq_mul_right_of_dvd at n25
        obtain ⟨k,hk⟩ := n25
        rw [hk] at eq
        rw [show 25 * k * (m + 1) = 25 * (k * (m + 1)) by ring] at eq
        rw [Int.mul_eq_mul_left_iff] at eq

        have k_val: k = 1 := by
          let q1:= q.natAbs
          have q_prime: Nat.Prime q1 := by
            simp [q1]
            rw [Nat.prime_iff_prime_int]
            simp [Prime_q]
            have qq: |q| = q := by
              simp
              omega
            rw [qq]
            exact Prime_q
          let k1:= k.natAbs
          have qq1: q.natAbs = q1 := by simp [q1]
          have kk1: k.natAbs = k1 := by simp [k1]
          have kq: k ∣ q := by rw [eq]; apply dvd_mul_right
          rw [←Int.natAbs_dvd_natAbs] at kq
          rw [qq1] at kq
          rw [kk1] at kq
          apply Nat.Prime.eq_one_or_self_of_dvd at kq
          replace kq: k = 1 ∨ k = q := by omega
          rcases kq with kq | kq
          . exact kq
          . rw [kq] at eq
            have no: q > q := by
              calc
                q = q * (m + 1) := by omega
                  _> q * 1 := by nlinarith
                  _ = q := by ring
            omega
          . exact q_prime

        simp [k_val] at hk eq
        have p_va: q = 27 := by omega
        rw [p_va] at Prime_q
        norm_num at Prime_q
        omega
      -- 25 ∣ n + 1 --
      . apply exists_eq_mul_right_of_dvd at n25
        obtain ⟨k,hk⟩ := n25
        rw [hk] at eq
        rw [show (m - 1) * (25 * k) = 25 * (k * (m - 1)) by ring] at eq
        rw [Int.mul_eq_mul_left_iff] at eq

        have k_val: k = 1 := by
          let q1:= q.natAbs
          have q_prime: Nat.Prime q1 := by
            simp [q1]
            rw [Nat.prime_iff_prime_int]
            simp [Prime_q]
            have qq: |q| = q := by
              simp
              omega
            rw [qq]
            exact Prime_q
          let k1:= k.natAbs
          have qq1: q.natAbs = q1 := by simp [q1]
          have kk1: k.natAbs = k1 := by simp [k1]
          have kq: k ∣ q := by rw [eq]; apply dvd_mul_right
          rw [←Int.natAbs_dvd_natAbs] at kq
          rw [qq1] at kq
          rw [kk1] at kq
          apply Nat.Prime.eq_one_or_self_of_dvd at kq
          replace kq: k = 1 ∨ k = q := by omega
          rcases kq with kq | kq
          . exact kq
          . rw [kq] at eq
            have no: q > q := by
              calc
                q = q * (m - 1) := by omega
                  _> q * 1 := by nlinarith
                  _ = q := by ring
            omega
          . exact q_prime

        simp [k_val] at hk eq
        omega
        omega
     -- s = 4--
    . simp [hs] at *
      rcases hq with ⟨bn,hq⟩
      have eq: 25 * q = (m - 2) * (m + 2) := by
        simp [n_deup] at hq
        have eqr: (5 * r + 4) / 5 = r := by
          ring_nf
          omega
        rw [eqr] at hq
        replace hq: 25 * q = 5 * r := by omega
        replace n_deup:  5 * r = m ^ 2 - 4 := by omega
        rw [n_deup] at hq
        ring_nf
        omega
      have dvd25: 25 ∣ (m - 2) * (m + 2) := by
        omega
      have n25: 25 ∣ m - 2 ∨ 25 ∣ m + 2 := by
        specialize mod25_2 m
        apply mod25_2
        omega
        exact dvd25
      rcases n25 with n25 | n25
      -- 25 ∣ n - 2 --
      . apply exists_eq_mul_right_of_dvd at n25
        obtain ⟨k,hk⟩ := n25
        rw [hk] at eq
        rw [show 25 * k * (m + 2) = 25 * (k * (m + 2)) by ring] at eq
        rw [Int.mul_eq_mul_left_iff] at eq

        have k_val: k = 1 := by
          let q1:= q.natAbs
          have q_prime: Nat.Prime q1 := by
            simp [q1]
            rw [Nat.prime_iff_prime_int]
            simp [Prime_q]
            have qq: |q| = q := by
              simp
              omega
            rw [qq]
            exact Prime_q
          let k1:= k.natAbs
          have qq1: q.natAbs = q1 := by simp [q1]
          have kk1: k.natAbs = k1 := by simp [k1]
          have kq: k ∣ q := by rw [eq]; apply dvd_mul_right
          rw [←Int.natAbs_dvd_natAbs] at kq
          rw [qq1] at kq
          rw [kk1] at kq
          apply Nat.Prime.eq_one_or_self_of_dvd at kq
          replace kq: k = 1 ∨ k = q := by omega
          rcases kq with kq | kq
          . exact kq
          . rw [kq] at eq
            have no: q > q := by
              calc
                q = q * (m + 2) := by omega
                  _> q * 1 := by nlinarith
                  _ = q := by ring
            omega
          . exact q_prime

        simp [k_val] at hk eq
        omega
        omega
      -- 25 ∣ n + 2 --
      . apply exists_eq_mul_right_of_dvd at n25
        obtain ⟨k,hk⟩ := n25
        rw [hk] at eq
        rw [show (m - 2) * (25 * k) = 25 * (k * (m - 2)) by ring] at eq
        rw [Int.mul_eq_mul_left_iff] at eq

        have k_val: k = 1 := by
          let q1:= q.natAbs
          have q_prime: Nat.Prime q1 := by
            simp [q1]
            rw [Nat.prime_iff_prime_int]
            simp [Prime_q]
            have qq: |q| = q := by
              simp
              omega
            rw [qq]
            exact Prime_q
          let k1:= k.natAbs
          have qq1: q.natAbs = q1 := by simp [q1]
          have kk1: k.natAbs = k1 := by simp [k1]
          have kq: k ∣ q := by rw [eq]; apply dvd_mul_right
          rw [←Int.natAbs_dvd_natAbs] at kq
          rw [qq1] at kq
          rw [kk1] at kq
          apply Nat.Prime.eq_one_or_self_of_dvd at kq
          replace kq: k = 1 ∨ k = q := by omega
          rcases kq with kq | kq
          . exact kq
          . rw [kq] at eq
            have no: q > q := by
              calc
                q = q * (m - 2) := by omega
                  _> q * 1 := by nlinarith
                  _ = q := by ring
            omega
          . exact q_prime

        simp [k_val] at hk eq
        have p_val: q = 21 := by omega
        rw [p_val] at Prime_q
        norm_num at Prime_q
        omega

  omega
