import Mathlib

/-Find all prime numbers p such that
p ^ x = y ^ 3 + 1
holds, where x,y are positive integers.-/

theorem number_theory_148760:
  {p: ℤ | 0 < p ∧ Prime p ∧ ∃ x: ℕ, 0 < x ∧ (∃ y: ℤ, 0 < y ∧ p ^ x = y ^ 3 + 1)} = {2, 3} := by

  ext p
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    rcases h with ⟨lp, hp, h⟩
    obtain ⟨x, hx, y, hy, h⟩ := h
    simp
    by_contra! ne
    rw [show y ^ 3 + 1 = (y + 1) * (y ^ 2 - y + 1) by ring] at h

    -- then we write y+1 as pow of p
    have f: ∃ t: ℕ, t ≤ x ∧ y + 1 = p ^ t := by
      replace h: (p ^ x).natAbs = (y + 1).natAbs * (y ^ 2 - y + 1).natAbs := by
        rw [h]
        rw [Int.natAbs_mul]
      rw [Int.natAbs_pow] at h
      replace h: (y + 1).natAbs ∣ (p.natAbs) ^ x := by
        rw [h]
        simp
      rw [Nat.dvd_prime_pow] at h
      obtain ⟨t, f⟩ := h
      rcases f with ⟨f, g⟩
      zify at g
      rw [show |y + 1| = y + 1 by apply abs_of_nonneg; omega] at g
      rw [show |p| = p by apply abs_of_nonneg; omega] at g
      use t
      rw [← Int.prime_iff_natAbs_prime]
      exact hp
    obtain ⟨t, f⟩ := f
    rcases f with ⟨ht, g⟩

    simp [g] at h
    replace g: y = p ^ t - 1 := by omega
    simp [g] at h
    ring_nf at h
    rw [show x = x - t + t by omega] at h
    ring_nf at h
    rw [show p ^ (t * 2) = p ^ t * p ^ t by ring] at h
    rw [show p ^ (t * 3) = p ^ t * p ^ (t * 2) by ring] at h
    replace h: p ^ (x - t) = 3 - p ^ t * 3 + p ^ (t * 2) := by nlinarith

    -- then we show that x ≤ 3t
    have l: x ≤ 3 * t := by
      suffices u: p ^ (x - t) ≤ p ^ (t * 2) by
        rw [pow_le_pow_iff_right₀] at u
        omega
        by_contra! f
        replace f: p = 1 := by omega
        simp [f] at hp
      rw [h]
      suffices v: 3 ≤ p ^ t * 3 by omega
      suffices 0 < p ^ t by omega
      apply Lean.Omega.Int.pos_pow_of_pos
      omega
    replace h: p ^ (x - t) * (p ^ (3 * t - x) - 1) = 3 * (p ^ t - 1) := by
      ring_nf
      have q: p ^ (x - t) * p ^ (t * 3 - x) = p ^ (t * 2) := by
        rw [show t * 2 = x - t + (t * 3 - x) by omega]
        ring
      rw [q]
      simp [h]
      ring
    have d: 3 ∣ p ^ (x - t) * (p ^ (3 * t - x) - 1) := by
      rw [h]
      simp
    apply Prime.dvd_or_dvd at d
    rcases d with d | d

    -- case 1
    .
      apply Prime.dvd_of_dvd_pow at d
      rw [← Int.natAbs_dvd_natAbs] at d
      simp at d
      rw [Nat.prime_dvd_prime_iff_eq] at d
      zify at d
      rw [show |p| = p by apply abs_of_nonneg; omega] at d
      simp [← d] at ne
      norm_num
      rw [← Int.prime_iff_natAbs_prime]
      exact hp
      norm_num

    -- case 2
    .
      apply exists_eq_mul_right_of_dvd at d
      obtain ⟨c, hc⟩ := d
      simp [hc] at h
      have lc: 0 ≤ c := by
        suffices 0 < p ^ (3 * t - x) by omega
        apply Lean.Omega.Int.pos_pow_of_pos
        omega

      replace h: p ^ (x - t) * c = (p ^ t - 1) := by nlinarith
      have c: p ∣ 1 := by
        rw [show 1 = p ^ t - p ^ (x - t) * c by rw [h]; omega]
        apply dvd_sub
        .
          rw [show t= t - 1 + 1 by omega]
          ring_nf
          simp
        .
          have s: t < x := by
            suffices t ≠ x by omega
            by_contra! o
            simp [o] at h hc
            replace h: p ^ x = c + 1 := by omega
            rw [show 3 * x - x = 2 * x by omega] at hc
            rw [show p ^ (2 * x) = (p ^ x) ^ 2 by ring] at hc
            simp [h] at hc
            ring_nf at hc
            by_cases j: c = 0

            -- c = 0
            .
              simp [j] at h
              rw [pow_eq_one_iff_cases] at h
              rcases h with h | h | h
              .
                simp [h] at hx
              .
                simp [h] at hp
              .
                simp [h] at lp

            -- c = 1
            .
              replace hc: c * 2 + c ^ 2 - c * 3 = 0 := by linarith
              rw [show c * 2 + c ^ 2 - c * 3 = c * (2 + c - 3) by ring] at hc
              simp at hc
              simp [j] at hc
              replace hc: c = 1 := by omega
              simp [hc] at h
              have lp: 4 ≤ p := by
                suffices p ≠ 1 by omega
                by_contra! o
                simp [o] at hp
              have c: 4 ^ 1 ≤ 2 := by
                zify
                rw [← h]
                have s1: 4 ^ 1 ≤ 4 ^ x := by
                  apply pow_le_pow_right₀
                  norm_num
                  omega
                have s2: 4 ^ x ≤ p ^ x := by
                  apply pow_le_pow_left₀
                  norm_num
                  omega
                nlinarith
              norm_num at c

          rw [show x - t = x - t - 1 + 1 by omega]
          ring_nf
          rw [show p * p ^ (x - t - 1) * c = p * (p ^ (x - t - 1) * c) by ring]
          simp

      apply exists_eq_mul_right_of_dvd at c
      obtain ⟨q, hq⟩ := c
      have lq: 1 ≤ q := by nlinarith
      have z: p ≤ 1 := by nlinarith
      have u: p = 1 := by omega
      simp [u] at hp

    norm_num


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
      norm_num
      use 1
      norm_num
      use 1
      norm_num
    .
      simp [h]
      norm_num
      use 2
      norm_num
      use 2
      norm_num