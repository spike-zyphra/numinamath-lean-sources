import Mathlib

lemma cube_sub_one_eq (m: ℕ) (hm: 1 ≤ m): m ^ 3 - 1 = (m - 1) * (m ^ 2 + m + 1) := by
  zify
  have e1: ↑(m ^ 3 - (1: ℕ)) = ↑(m ^ 3) - (1: ℤ) := by
    apply Int.natCast_sub
    rw [show m ^ 3 = m * m ^ 2 by ring]
    nlinarith
  have e2: ↑(m - (1: ℕ)) = ↑(m) - (1: ℤ) := by
    apply Int.natCast_sub
    nlinarith
  rw [e1, e2]
  clear e1 e2
  have e3: ↑(m ^ 3) = (m: ℤ) ^ 3 := by
    apply Int.natCast_pow
  rw [e3]
  ring

/- Determine all primes $p$ and all non-negative integers $m$ and $n$, such that $$1 + p^n = m^3. $$ -/

theorem number_theory_84728:
    {(p, m, n): ℕ × ℕ × ℕ | Nat.Prime p ∧ 1 + p ^ n = m ^ 3} = {(7, 2, 1)} := by

  ext ⟨p, m, n⟩
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    simp
    rcases h with ⟨hp, h⟩
    have lm: 1 ≤ m := by
      by_contra! o
      replace o: m = 0 := by omega
      simp [o] at h
    replace h: p ^ n = m ^ 3 - 1 := by
      omega

    -- use lemma to factor right hand side
    rw [cube_sub_one_eq] at h

    -- then we can write both as power of p
    have s: m - 1 ∣ p ^ n := by
      rw [h]
      simp
    rw [Nat.dvd_prime_pow] at s
    obtain ⟨a, s⟩ := s
    have t: m ^ 2 + m + 1 ∣ p ^ n := by
      rw [h]
      simp
    rw [Nat.dvd_prime_pow] at t
    obtain ⟨b, t⟩ := t
    rcases s with ⟨la, ha⟩
    rcases t with ⟨lb, hb⟩
    rw [ha, hb] at h
    rw [show p ^ a * p ^ b = p ^ (a + b) by ring] at h
    rw [pow_right_inj₀] at h
    clear la lb
    replace ha: m = p ^ a + 1 := by omega
    simp [ha] at hb
    ring_nf at hb
    clear lm
    by_cases la: a = 0

    -- case a = 0
    .
      simp [la] at hb
      have lb: 1 ≤ b := by
        by_contra! o
        replace o: b = 0 := by omega
        simp [o] at hb
      rw [show b = b - 1 + 1 by omega] at hb
      rw [Nat.pow_succ] at hb
      have o: p ≤ 7 := by
        rw [hb]
        apply Nat.le_of_dvd
        omega
        simp
      interval_cases p
      all_goals norm_num at hp
      .
        have o: 2 ∣ 7 := by
          rw [hb]
          simp
        norm_num at o
      .
        have o: 3 ∣ 7 := by
          rw [hb]
          simp
        norm_num at o
      .
        have o: 5 ∣ 7 := by
          rw [hb]
          simp
        norm_num at o
      .
        by_contra! s
        replace hb: 7 ^ (b - 1) = 1 := by omega
        rw [pow_eq_one_iff] at hb
        norm_num at hb
        by_contra! q
        replace q: b = 1 := by omega
        absurd s
        simp
        simp [la, q] at *
        simp [ha] at s
        simp [h] at s

    -- case a > 0
    .
      -- we show that p ∣ 3
      have lb: 1 ≤ b := by
        by_contra! o
        replace o: b = 0 := by omega
        simp [o] at hb
        omega
      replace la: 1 ≤ a := by omega
      have d: (3 + p ^ a * 3 + p ^ (a * 2)) % p  = (p ^ b) % p := by
        rw [hb]
      have o1: p ^ b % p = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        rw [show b = b - 1 + 1 by omega]
        rw [Nat.pow_succ]
        simp
      rw [o1] at d
      clear o1
      rw [Nat.add_mod] at d
      have o2: p ^ (a * 2) % p = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        rw [show a * 2 = a * 2 - 1 + 1 by omega]
        rw [Nat.pow_succ]
        simp
      rw [o2] at d
      clear o2
      rw [show 0 = 0 % p by simp] at d
      rw [← Nat.add_mod] at d
      norm_num at d
      rw [Nat.add_mod] at d
      have o3: p ^ a % p = 0 := by
        apply Nat.mod_eq_zero_of_dvd
        rw [show a = a - 1 + 1 by omega]
        rw [Nat.pow_succ]
        simp
      rw [Nat.mul_mod] at d
      rw [o3] at d
      simp at d
      apply Nat.dvd_of_mod_eq_zero at d
      clear o3

      -- hence p = 3
      rw [Nat.prime_dvd_prime_iff_eq] at d
      simp [d] at *
      clear hp d

      -- then we must have b ≤ 1 by mod 9
      have rb: b ≤ 1 := by
        by_contra! r
        have o: 9 ∣ 3 ^ b := by
          rw [show b = b - 2 + 2 by omega]
          rw [Nat.pow_succ]
          rw [Nat.pow_succ]
          rw [show 3 ^ (b - 2) * 3 * 3 = 3 ^ (b - 2) * 9 by ring]
          simp
        rw [← hb] at o
        have c: 9 ∣ 3 := by
          rw [show 3 = 3 + 3 ^ a * 3 + 3 ^ (a * 2) - (3 ^ a * 3 + 3 ^ (a * 2)) by omega]
          apply Nat.dvd_sub
          omega
          exact o
          apply Nat.dvd_add
          rw [show a = a - 1 + 1 by omega]
          rw [Nat.pow_succ]
          rw [show 3 ^ (a - 1) * 3 * 3 = 3 ^ (a - 1) * 9 by ring]
          simp
          rw [show a * 2 = (a - 1) * 2 + 2 by omega]
          rw [Nat.pow_succ]
          rw [Nat.pow_succ]
          rw [show 3 ^ ((a - 1) * 2) * 3 * 3 = 3 ^ ((a - 1) * 2) * 9 by ring]
          simp
        norm_num at c

      -- then b = 1, contradiction arises from hb
      have o: b = 1 := by omega
      simp [o] at hb
      have v: 0 < 3 ^ a := by
        apply Nat.pos_pow_of_pos
        norm_num
      have u: 0 < 3 ^ (a * 2) := by
        apply Nat.pos_pow_of_pos
        norm_num
      have c: 3 < 3 + 3 ^ a * 3 + 3 ^ (a * 2) := by
        omega
      simp [hb] at c
      exact hp
      norm_num

    .
      by_contra! l
      interval_cases p
      .
        norm_num at hp
    .
      by_contra! o
      simp [o] at hp
      norm_num at hp
    .
      exact hp
    .
      exact hp
    .
      omega


  -- the backward direction
  .
    intro h
    simp at h
    simp [h]
    norm_num
