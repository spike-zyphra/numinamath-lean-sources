import Mathlib

/-The sum of 2 positive integers is 156.
Find the sum of all possible values of their greatest common divisor.
The sum of 2 positive integers is 156. Find the sum of all possible values of their greatest common factor.-/

theorem number_theory_630163:
    ∑ᶠ x ∈ {n: ℕ | ∃ a b: ℕ, 0 < a ∧ 0 < b ∧ a + b = 156 ∧ n = a.gcd b}, x = 236 := by

    -- we directly compute the set
    have h_eq: {n: ℕ | ∃ a b: ℕ, 0 < a ∧ 0 < b ∧ a + b = 156 ∧ n = a.gcd b} =
      {1, 2, 3, 4, 6, 12, 13, 26, 39, 52, 78} := by
      ext n
      constructor
      -- the forward direction
      .
        intro h
        simp at h
        obtain ⟨a, ha, b, hb, h, hn⟩ := h
        simp [hn]
        clear hn
        replace h: b = 156 - a := by omega
        rw [h]
        replace hb: a < 156 := by omega
        have o: a.gcd (156 - a) = a.gcd 156 := by
          rw [← Nat.gcd_self_add_right]
          rw [show a + (156 - a) = 156 by omega]
        rw [o]
        clear o
        interval_cases a
        all_goals decide

      -- the backward direction
      .
        intro h
        simp at h
        rcases h with h | h | h | h | h | h | h | h | h | h | h
        all_goals simp [h]; clear h
        .
          use 1
          norm_num
          use 155
          norm_num
        .
          use 2
          norm_num
          use 154
          norm_num
        .
          use 3
          norm_num
          use 153
          norm_num
        .
          use 4
          norm_num
          use 152
          norm_num
        .
          use 6
          norm_num
          use 150
          norm_num
        .
          use 12
          norm_num
          use 144
          norm_num
        .
          use 13
          norm_num
          use 143
          norm_num
        .
          use 26
          norm_num
          use 130
          norm_num
        .
          use 39
          norm_num
          use 117
          norm_num
        .
          use 52
          norm_num
          use 104
          norm_num
        .
          use 78
          norm_num
          use 78
          norm_num


    -- then we compute the sum
    rw [h_eq]
    rw [finsum_mem_eq_toFinset_sum]
    simp