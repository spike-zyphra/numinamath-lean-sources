import Mathlib

/-Find all pairs
(a,b) of positive integers such that a^3 is a multiple of b^2 and
b−1 is a multiple of a−1. Note: An integer
n is said to be a multiple of an integer m if there is an integer k such that n=km.-/

theorem number_theory_606253: {(a, b): ℕ × ℕ | 0 < a ∧ 0 < b ∧ (∃ c: ℕ, a ^ 3 = b ^ 2 * c)
∧ (∃ d: ℕ, b - 1 = (a - 1) * d)} = {(a, b): ℕ × ℕ | (0 < a ∧ a = b) ∨ (0 < a ∧ b = 1)} := by

  ext ⟨a,b⟩
  simp only [Set.mem_setOf_eq]
  constructor
  -- forward direction
  .
    intro h
    rcases h with ⟨ha,hb,h1,h2⟩
    obtain ⟨c, h1⟩ := h1
    obtain ⟨d, h2⟩ := h2
    by_cases l: b < a
    -- case 1: b < a
    .
      have o: b = 1 := by
        by_contra! o
        have d: a - 1 ∣ b - 1 := by
          rw [h2]
          simp
        apply Nat.le_of_dvd at d
        simp at d
        rw [show b - 1 + 1 = b by omega] at d
        omega
        omega
      right
      omega
    -- case 2: b ≥ a
    .
      by_cases i: a = 1
      -- case 2.1: a = 1
      .
        simp [i] at h2
        left
        omega
      -- case 2.2: a > 1
      .
        simp at l
        replace ha: 2 ≤ a := by omega
        clear i
        have hc: 0 < c := by
          by_contra! o
          replace o: c = 0 := by omega
          simp [o] at h1
          omega
        set e:= a - 1 with he
        have le: 0 < e := by
          omega
        have h3: a - 1 ∣ c - 1 := by
           -- we show that a - 1 ∣ c - 1
           rw [← he]
           replace he: a = e + 1 := by omega
           replace h2: b = e * d + 1 := by omega
           simp [he,h2] at h1
           replace h1: (e + 1) ^ 3 - 1 = (e * d + 1) ^ 2 * c - 1 := by omega
           have d1: e ∣ (e + 1) ^ 3 - 1 := by
            have eq: (e + 1) ^ 3 - 1 = e * (e ^ 2 + 3 * e + 3) := by
              ring_nf
              omega
            rw [eq]
            simp
           rw [h1] at d1
           have eq: (e * d + 1) ^ 2 * c - 1 = e * (c * (e * d ^ 2 + 2 * d)) + (c - 1) := by
            ring_nf
            omega
           rw [eq] at d1
           rw [show c - 1 = e * (c * (e * d ^ 2 + 2 * d)) + (c - 1) - e * (c * (e * d ^ 2 + 2 * d)) by omega]
           apply Nat.dvd_sub
           . omega
           . exact d1
           . simp
        simp [e] at h2
        clear le he
        clear_value e
        by_cases lc: c < a
        -- case 2.2.1: c < a
        .
          -- then c = 1
          have o: c = 1 := by
            by_contra! o
            replace o: 0 < c - 1 := by omega
            apply Nat.le_of_dvd at h3
            replace he: a ≤ c := by omega
            omega
            exact o
          simp [o] at *
          clear hc o h3
          -- now we write a = p ^ 2 , b = p ^ 3
          have s: a ^ 2 ∣ b ^ 2 := by
            rw [← h1]
            rw [show a ^ 3 = a ^ 2 * a by ring]
            simp
          rw [Nat.pow_dvd_pow_iff] at s
          apply exists_eq_mul_right_of_dvd at s
          obtain ⟨p, hp⟩ := s
          simp [hp] at h1
          replace h1: a = p ^ 2 := by nlinarith
          simp [h1] at hp
          ring_nf at hp
          rw [h1,hp] at h2
          have lp: 0 < p := by
            by_contra! o
            replace o: p = 0 := by omega
            simp [o] at h1
            omega
          -- then we factor h2
          have eq: p ^ 3 - 1 = (p - 1) * (p * (p + 1) + 1) := by
            ring_nf
            zify
            rw [Int.natCast_sub]
            rw [Int.natCast_sub]
            rw [Int.natCast_pow]
            ring
            omega
            omega
          rw [eq] at h2
          clear eq
          have eq: p ^ 2 - 1 = (p - 1) * (p + 1) := by
            ring_nf
            zify
            rw [Int.natCast_sub]
            rw [Int.natCast_sub]
            rw [Int.natCast_pow]
            ring
            omega
            omega
          rw [eq] at h2
          clear eq
          by_cases op: p = 1
          -- case 1: p = 1
          .
            simp [op] at *
            omega
          -- case 2: p > 1
          .
            replace op: 0 < p - 1 := by omega
            replace h2: p * (p + 1) + 1 = (p + 1) * d := by
              rw [show (p - 1) * (p + 1) * d = (p - 1) * ((p + 1) * d) by ring] at h2
              apply Nat.eq_of_mul_eq_mul_left op h2
            have f: p + 1 ∣ p * (p + 1) + 1 := by
              rw [h2]
              apply Nat.dvd_mul_right
            have g: p + 1 ∣ 1 := by
              nth_rewrite 2 [show 1 = (p * (p + 1) + 1) - p * (p + 1) by omega]
              apply Nat.dvd_sub
              . omega
              . exact f
              . simp
            apply Nat.le_of_dvd at g
            omega
            norm_num
          norm_num
        -- case 2.2.2: c ≥ a
        .
          -- then we show that a = b
          left
          have u: 0 < a := by omega
          refine ⟨u, ?_⟩
          by_contra! r
          replace r: a < b := by omega
          have contra: b ^ 2 * c <  b ^ 2 * c := by
            have t: a ^ 2 < b ^ 2 := by
              apply Nat.pow_lt_pow_left
              . omega
              . omega
            calc
              b ^ 2 * c = a ^ 3 := by omega
                      _ = a ^ 2 * a := by ring
                      _ < b ^ 2 * a := by nlinarith
                      _ ≤ b ^ 2 * c := by nlinarith
          omega


  -- backward direction
  .
    intro h
    rcases h with h1 | h2
    .
      rcases h1 with ⟨ha,h⟩
      simp [h]
      rw [← h]
      simp [ha]
      constructor
      .
        use a
        simp [h]
        ring
      .
        use 1
        omega
    .
      rcases h2 with ⟨ha,h⟩
      simp [h,ha]