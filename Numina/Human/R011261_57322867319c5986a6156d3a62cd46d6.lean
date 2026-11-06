import Mathlib

-- we show a lemma to write the perfect square as a square of a positive integer
lemma lemma_1 (a: ℤ) (ha: 0 < a) (h: IsSquare a): ∃ b, 0 < b ∧ a = b ^ 2 := by
  apply IsSquare.exists_sq at h
  obtain ⟨b, hb⟩ := h
  by_cases l: 0 < b
  .
    use b
  .
    set c:= -b
    have o: 0 < c := by
      simp [c]
      simp at l
      have f: b ≠ 0 := by
        by_contra! f
        simp [f] at hb
        simp [hb] at ha
      omega
    use c
    simp [o]
    simp [c]
    exact hb

/-Find all pairs of prime numbers p and q for which the numbers
p+q and p+4q are perfect squares.-/

theorem number_theory_131336: {(p, q): ℤ × ℤ | 0 < p ∧ 0 < q ∧
Prime p ∧ Prime q ∧ IsSquare (p + q) ∧ IsSquare (p + 4 * q)} =
  {(5, 11), (13, 3)} := by

  ext ⟨p, q⟩
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    rcases h with ⟨lp, lq, hp, hq, h1, h2⟩
    replace h1:= lemma_1 (p + q) (by linarith) h1
    obtain ⟨x, h1⟩ := h1
    replace h2:= lemma_1 (p + 4 * q) (by linarith) h2
    obtain ⟨y, h2⟩ := h2
    have l: x < y := by nlinarith
    rcases h1 with ⟨lx, h1⟩
    rcases h2 with ⟨ly, h2⟩

    -- then we have the key factorization
    replace h2: 3 * q = (y - x) * (y + x) := by
      nlinarith
    have d: q ∣ (y - x) * (y + x) := by
      rw [← h2]
      simp
    apply Prime.dvd_or_dvd at d
    rcases d with d | d

    -- case 1
    .
      apply exists_eq_mul_right_of_dvd at d
      obtain ⟨k, hk⟩ := d
      have lk: 0 < k := by nlinarith
      simp [hk] at h2
      replace h2: 3 = k * (y + x) := by nlinarith
      have rk: k ≤ 3 := by nlinarith
      interval_cases k

      -- k = 1
      .
        simp at h2
        have rq: q < 3 := by omega
        interval_cases q
        .
          norm_num at hq
        .
          have vx: x = 1 := by omega
          simp [vx] at h1
          omega

      -- k = 2
      .
        have c: 2 ∣ 3 := by
          zify
          rw [h2]
          simp
        norm_num at c

      -- k = 3
      .
        replace h2: y + x = 1 := by omega
        omega

    -- case 2
    .
      apply exists_eq_mul_right_of_dvd at d
      obtain ⟨k, hk⟩ := d
      have lk: 0 < k := by nlinarith
      simp [hk] at h2
      replace h2: 3 = k * (y - x) := by nlinarith
      have rk: k ≤ 3 := by nlinarith
      interval_cases k

      -- k = 1
      .
        have vq: q = 2 * x + 3 := by omega
        simp [vq] at h1
        replace h1: p  = x ^ 2 - (2 * x + 3) := by omega
        rw [show x ^ 2 - (2 * x + 3) = (x + 1) * (x - 3) by ring] at h1
        have o: p ∣ (x + 1) * (x - 3) := by
          rw [h1]
        rw [Prime.dvd_mul] at o
        rcases o with o | o
        .
          apply exists_eq_mul_right_of_dvd at o
          obtain ⟨k, hk⟩ := o
          have lk: 0 < k := by nlinarith
          simp [hk] at h1
          have vx: x = 4 := by nlinarith
          simp [vx] at hk h1
          have vp: p = 5 := by omega
          simp [vx] at vq
          simp [vp, vq]
        .
          apply exists_eq_mul_right_of_dvd at o
          obtain ⟨k, hk⟩ := o
          simp [hk] at h1
          replace h1: (x + 1) * k = 1 := by nlinarith
          have s: x + 1 ∣ 1 := by
            nth_rewrite 2 [← h1]
            simp
          rw [← Int.natAbs_dvd_natAbs] at s
          simp at s
          zify at s
          rw [show |x + 1| = x + 1 by apply abs_of_pos; omega] at s
          omega
        exact hp

      -- k = 2
      .
        have c: 2 ∣ 3 := by
          zify
          rw [h2]
          simp
        norm_num at c

      -- k = 3
      .
        replace h2: y - x = 1 := by omega

        -- then q is odd
        have oq: Odd q := by
          rw [← Int.natAbs_odd]
          apply Nat.Prime.odd_of_ne_two
          .
            rw [← Int.prime_iff_natAbs_prime]
            exact hq
          .
            zify
            rw [show |q| = q by apply abs_of_pos; omega]
            by_contra! f
            simp [f] at hk
            have c: 2 * y = 7 := by omega
            have c1: 2 ∣ 7 := by
              zify
              rw [← c]
              simp
            norm_num at c1
        apply Odd.exists_bit1 at oq
        obtain ⟨m, hm⟩ := oq
        have lm: 0 ≤ m := by nlinarith
        have vx: x = 3 * m + 1 := by omega

        -- then we have the following factorization
        have vp: p = m * (9 * m + 4) := by nlinarith
        have dp: p ∣ m * (9 * m + 4) := by
          rw [vp]
        rw [Prime.dvd_mul] at dp
        rcases dp with dp | dp
        -- case 1
        .
          apply exists_eq_mul_right_of_dvd at dp
          obtain ⟨k, hk⟩ := dp
          have lk: 0 ≤ k := by nlinarith
          nth_rewrite 1 [hk] at vp
          replace vp: k * (9 * m + 4) = 1 := by nlinarith
          have rk: k ≤ 1 := by nlinarith
          have vk: k = 0 ∨ k = 1 := by omega
          rcases vk with t | t
          .
            simp [t] at vp
          .
            simp [t] at vp
            nlinarith
        -- case 2
        .
          apply exists_eq_mul_right_of_dvd at dp
          obtain ⟨u, hu⟩ := dp
          have lu: 0 ≤ u := by nlinarith
          rw [hu] at vp
          replace vp: m * u = 1 := by nlinarith
          have lm: 0 ≤ m := by nlinarith
          have i: m ∣ 1 := by
            rw [← vp]
            simp
          rw [← Int.natAbs_dvd_natAbs] at i
          simp at i
          zify at i
          rw [show |m| = m by apply abs_of_nonneg; linarith] at i
          simp [i] at *
          simp [vx] at h2
          replace h2: y = 5 := by omega
          simp [h2, vx] at *
          right
          omega

        exact hp

    exact hq


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
      norm_num
      native_decide
    .
      simp [h]
      norm_num
      native_decide