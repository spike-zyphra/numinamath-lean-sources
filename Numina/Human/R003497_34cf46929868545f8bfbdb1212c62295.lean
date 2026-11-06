import Mathlib

-- we show a mod lemma which will be used later
lemma lemma_1 (x: ℤ) (h: 9 ∣ x ^ 3 - x): x % 9 = 0 ∨ x % 9 = 1 ∨ x % 9 = 8 := by
  rw [show x ^ 3 - x = x * (x - 1) * (x + 1) by ring] at h
  have i: 3 ∣ x ∨ 3 ∣ x - 1 ∨ 3 ∣ x + 1 := by
    omega
  rcases i with i | i | i

  -- case 3 ∣x
  .
    apply exists_eq_mul_right_of_dvd at i
    obtain ⟨q, hq⟩ := i
    simp [hq] at h
    rw [show 3 * q * (3 * q - 1) * (3 * q + 1) = 3 * (q * (3 * q - 1) * (3 * q + 1)) by ring] at h
    rw [show (9: ℤ) = 3 * 3 by norm_num] at h
    apply Int.dvd_of_mul_dvd_mul_left at h
    simp [hq]
    suffices 3 ∣ q by
      left
      rw [show (9: ℤ) = 3 * 3 by norm_num]
      apply Int.mul_dvd_mul
      norm_num
      tauto
    rw [Prime.dvd_mul] at h
    rcases h with h | h
    .
      rw [Prime.dvd_mul] at h
      rcases h with h | h
      .
        tauto
      .
        replace h: 3 ∣ 1 := by
          zify
          rw [show 1 = 3 * q - (3 * q - 1) by ring]
          apply dvd_sub
          .
            simp
          .
            tauto
        norm_num at h
      .
        norm_num
    .
        replace h: 3 ∣ 1 := by
          zify
          rw [show 1 = 3 * q + 1 - 3 * q by ring]
          apply dvd_sub
          .
            tauto
          .
            simp
        norm_num at h
    norm_num
    norm_num

  -- case 3 ∣ x - 1
  .
    apply exists_eq_mul_right_of_dvd at i
    obtain ⟨q, hq⟩ := i
    simp [hq] at h
    replace hq: x = 3 * q + 1 := by
      omega
    simp [hq] at *
    rw [show (3 * q + 1) * (3 * q) * (3 * q + 1 + 1) = 3 * ((3 * q + 1) * q * (3 * q + 1 + 1)) by ring] at h
    rw [show (9: ℤ) = 3 * 3 by norm_num] at h
    apply Int.dvd_of_mul_dvd_mul_left at h
    suffices 3 ∣ q by
      right
      left
      rw [Int.add_emod]
      suffices 3 * q % 9 = 0 by
        simp [this]
      rw [← Int.dvd_iff_emod_eq_zero]
      rw [show (9: ℤ) = 3 * 3 by norm_num]
      apply Int.mul_dvd_mul
      norm_num
      tauto
    rw [Prime.dvd_mul] at h
    rcases h with h | h
    .
      rw [Prime.dvd_mul] at h
      rcases h with h | h
      .
        replace h: 3 ∣ 1 := by
          zify
          rw [show 1 = 3 * q + 1 - 3 * q by ring]
          apply dvd_sub
          .
            tauto
          .
            simp
        norm_num at h
      .
        tauto

      norm_num
    .
        replace h: 3 ∣ 2 := by
          zify
          rw [show 2 = 3 * q + 1 + 1 - 3 * q by ring]
          apply dvd_sub
          .
            tauto
          .
            simp
        norm_num at h
    norm_num
    norm_num

  -- case 3 ∣ x + 1
  .
    apply exists_eq_mul_right_of_dvd at i
    obtain ⟨q, hq⟩ := i
    simp [hq] at h
    replace hq: x = 3 * q - 1 := by
      omega
    simp [hq] at *
    rw [show (3 * q - 1) * (3 * q - 1 - 1) * (3 * q) = 3 * ((3 * q - 1) * (3 * q - 1 - 1) * q) by ring] at h
    rw [show (9: ℤ) = 3 * 3 by norm_num] at h
    apply Int.dvd_of_mul_dvd_mul_left at h
    suffices 3 ∣ q by
      right
      right
      rw [Int.sub_emod]
      suffices 3 * q % 9 = 0 by
        simp [this]
      rw [← Int.dvd_iff_emod_eq_zero]
      rw [show (9: ℤ) = 3 * 3 by norm_num]
      apply Int.mul_dvd_mul
      norm_num
      tauto
    rw [Prime.dvd_mul] at h
    rcases h with h | h
    .
      rw [Prime.dvd_mul] at h
      rcases h with h | h
      .
        replace h: 3 ∣ 1 := by
          zify
          rw [show 1 = 3 * q - (3 * q - 1) by ring]
          apply dvd_sub
          .
            tauto
          .
            tauto
        norm_num at h
      .
        replace h: 3 ∣ 2 := by
          zify
          rw [show 2 = 3 * q - (3 * q - 1 - 1) by ring]
          apply dvd_sub
          .
            tauto
          .
            tauto
        norm_num at h

      norm_num
    .
      tauto
    norm_num
    norm_num


-- a similar lemma for 11
lemma lemma_2 (x: ℤ) (h: 11 ∣ x ^ 3 - x): 11 ∣ x ∨ 11 ∣ x - 1 ∨ 11 ∣ x + 1 := by
  rw [show x ^ 3 - x = x * (x - 1) * (x + 1) by ring] at h
  rw [Prime.dvd_mul] at h
  rcases h with h | h
  .
    rw [Prime.dvd_mul] at h
    omega
    norm_num
  .
    omega
  norm_num


/-A two-digit number is appended to the right of a certain natural number,
and then another two-digit number is appended.
The resulting number turns out to be equal to the cube of the sum of the three original numbers.
Find all possible triples of the original numbers.-/

theorem number_theory_188736: {(a, b, c): ℤ × ℤ × ℤ | 0 < a ∧ 10 ≤ b ∧ b ≤ 99 ∧ 10 ≤ c ∧ c ≤ 99 ∧
  10000 * a + 100 * b + c = (a + b + c) ^ 3} = {(9, 11, 25)} := by

    ext ⟨a, b, c⟩
    constructor

    -- the forward direction
    .
      intro h
      simp at h
      rcases h with ⟨la, lb, rb, lc, rc, h⟩
      simp
      set x:= a + b + c

      -- we show that x ≤ 99
      have rx: x ≤ 99 := by
        by_contra! u
        have o: 10000 * a + 100 * b + c < x ^ 3 := by
          have l1: 10000 * a + 100 * b + c < 10000 * (a + b + c) := by
            omega
          rw [show a + b + c = x by simp [x]] at l1
          suffices 10000 * x ≤ x ^ 3 by
            linarith
          clear *- u
          clear_value x
          replace u: 100 ≤ x := by omega
          suffices 10000 ≤ x ^ 2 by
            rw [show x ^ 3 = x ^ 2 * x by ring]
            nlinarith
          nlinarith
        rw [h] at o
        simp at o

      -- then we show that 21 ≤ x
      have lx: 21 ≤ x := by
        clear h
        simp [x]
        nlinarith

      replace h: x ^ 3 - x =  9999 * a + 99 * b := by
        rw [← h]
        simp [x]
        ring

      -- then we use lemma_1 and lemma_2 to derive mod relations
      have d1: 11 ∣ x ^ 3 - x := by
        rw [h]
        rw [show 9999 * a + 99 * b = 11 * (909 * a + 9 * b) by ring]
        simp
      apply lemma_2 at d1
      have d2: 9 ∣ x ^ 3 - x := by
        rw [h]
        rw [show 9999 * a + 99 * b = 9 * (1111 * a + 11 * b) by ring]
        simp
      apply lemma_1 at d2

      rcases d1 with d | d | d

      -- case 11 ∣ x
      .
        apply exists_eq_mul_right_of_dvd at d
        obtain ⟨q, hq⟩ := d
        have lq: 2 ≤ q := by
          clear *- lx hq
          omega
        have rq: q ≤ 9 := by
          clear *- rx hq
          omega
        rw [hq] at d2
        have s: q = 4 ∨ q = 5 ∨ q = 9 := by
          by_contra! i
          clear *- d2 lq rq i
          interval_cases q
          all_goals omega
        rcases s with s | s | s

        -- q = 4, x = 44
        .
          simp [s] at hq
          simp [hq] at h
          simp [x] at hq
          have fa: a = 8 := by
            clear *- h la lb rb
            omega
          simp [fa] at h
          replace h: b = 52 := by
            clear *- h
            omega
          simp [fa, h] at hq
          clear *- hq lc
          omega

        -- q = 5, x = 55
        .
          simp [s] at hq
          simp [hq] at h
          simp [x] at hq
          have fa: a = 16 := by
            clear *- h la lb rb
            omega
          simp [fa] at h
          replace h: b = 64 := by
            clear *- h
            omega
          simp [fa, h] at hq
          clear *- hq lc
          omega

        -- q = 9, x = 99
        .
          simp [s] at hq
          simp [hq] at h
          simp [x] at hq
          have fa: a = 97 := by
            clear *- h la lb rb
            omega
          simp [fa] at h
          replace h: b = 3 := by
            clear *- h
            omega
          simp [fa, h] at hq
          clear *- hq lc
          omega

      -- case 11 ∣ x - 1
      .
        apply exists_eq_mul_right_of_dvd at d
        obtain ⟨q, hq⟩ := d
        replace hq: x = 11 * q + 1 := by
          clear *- hq
          omega
        have lq: 2 ≤ q := by
          clear *- lx hq
          omega
        have rq: q ≤ 8 := by
          clear *- rx hq
          omega
        rw [hq] at d2
        have s: q = 4 ∨ q = 8 := by
          by_contra! i
          clear *- d2 lq rq i
          interval_cases q
          all_goals omega
        rcases s with s | s

        -- q = 4, x = 45
        .
          simp [s] at hq
          simp [hq] at h
          simp [x] at hq
          have fa: a = 9 := by
            clear *- h la lb rb
            omega
          simp [fa] at h
          replace h: b = 11 := by
            clear *- h
            omega
          simp [fa, h] at hq
          clear *- hq lc h fa
          omega

        -- q = 8, x = 89
        .
          simp [s] at hq
          simp [hq] at h
          simp [x] at hq
          have fa: a = 70 := by
            clear *- h la lb rb
            omega
          simp [fa] at h
          replace h: b = 50 := by
            clear *- h
            omega
          simp [fa, h] at hq
          clear *- hq lc h fa
          omega

      -- case 11 ∣ x + 1
      .
        apply exists_eq_mul_right_of_dvd at d
        obtain ⟨q, hq⟩ := d
        replace hq: x = 11 * q - 1 := by
          clear *- hq
          omega
        have lq: 2 ≤ q := by
          clear *- lx hq
          omega
        have rq: q ≤ 9 := by
          clear *- rx hq
          omega
        rw [hq] at d2
        have s: q = 5 ∨ q = 9 := by
          by_contra! i
          clear *- d2 lq rq i
          interval_cases q
          all_goals omega
        rcases s with s | s

        -- q = 5, x = 54
        .
          simp [s] at hq
          simp [hq] at h
          simp [x] at hq
          have fa: a = 15 := by
            clear *- h la lb rb
            omega
          simp [fa] at h
          replace h: b = 75 := by
            clear *- h
            omega
          simp [fa, h] at hq
          clear *- hq lc h fa
          omega

        -- q = 9, x = 98
        .
          simp [s] at hq
          simp [hq] at h
          simp [x] at hq
          have fa: a = 94 := by
            clear *- h la lb rb
            omega
          simp [fa] at h
          replace h: b = 12 := by
            clear *- h
            omega
          simp [fa, h] at hq
          clear *- hq lc h fa
          omega


    -- the backward direction
    .
      intro h
      simp at h
      simp [h]