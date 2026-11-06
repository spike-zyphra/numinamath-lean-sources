import Mathlib

/-There are two four-digit numbers, their difference is 534,
and the last four digits of their square numbers are the same.
Then the larger four-digit numSber has ( ) possibilities. (A) 1 (B) 2 (C) 3 (D) 4-/

theorem number_theory_319195: {x : ℤ | ∃ y, 1000 ≤ x ∧ x < 10000 ∧ 1000 ≤ y ∧ y < 10000 ∧
  x - y = 534 ∧ (x ^ 2) % 10000 = (y ^ 2) % 10000}.encard = 3 := by

  -- we compute all possible values
    have h_eq: {x : ℤ | ∃ y, 1000 ≤ x ∧ x < 10000 ∧ 1000 ≤ y ∧ y < 10000 ∧
  x - y = 534 ∧ (x ^ 2) % 10000 = (y ^ 2) % 10000} = {2767, 5267, 7767} := by

      ext x
      constructor

      -- the forward direction
      .
        intro h
        simp only [Set.mem_setOf_eq] at h
        obtain ⟨y, lx, rx, ly, ry, h1, h2⟩ := h
        clear ry ly
        replace h2: (x ^ 2 - y ^ 2) % 10000 = 0 := by
          rw [Int.sub_emod]
          rw [h2]
          simp
        apply Int.dvd_of_emod_eq_zero at h2

        -- then we show that in fact 5000 ∣ x + y
        rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring] at h2
        rw [h1] at h2
        rw [show 534 * (x + y) = 267 * (2 * (x + y)) by ring] at h2
        apply IsCoprime.dvd_of_dvd_mul_left at h2
        rw [show (10000: ℤ) = 2 * 5000 by ring] at h2
        apply exists_eq_mul_right_of_dvd at h2
        obtain ⟨k, hk⟩ := h2
        replace h2: x + y = 5000 * k := by omega
        
        -- from the upper bound, we see that k is no more than 3
        have lk: 0 < k := by omega
        have rk: k < 4 := by nlinarith
        simp

        -- check k = 1, 2, 3 one by one
        interval_cases k
        .
          left
          nlinarith
        .
          right
          left
          nlinarith
        .
          right
          right
          nlinarith
        norm_num


      -- the backward direction
      .
        intro h
        simp at h
        rcases h with h | h | h
        .
          simp [h]
          use 2233
          norm_num
        .
          simp [h]
          use 4733
          norm_num
        .
          simp [h]
          use 7233
          norm_num


    -- finally, we can count the card
    rw [h_eq]
    simp [Set.encard]
    