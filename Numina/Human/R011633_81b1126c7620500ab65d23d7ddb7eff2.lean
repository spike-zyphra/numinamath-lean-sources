import Mathlib

/-Suppose that p and q are two different prime numbers and that
n=p^2q^2. The number of possible values of n with n < 1000
is (A) 5 (B) 6 (C) 4 (D) 8 (E) 7-/

theorem number_theory_267740:
    {n: ℕ | ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ n = p ^ 2 * q ^ 2 ∧ n < 1000}.encard = 7 := by

    -- we directly compute the set
    have h_eq: {n: ℕ | ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ n = p ^ 2 * q ^ 2 ∧ n < 1000}
      = {6 ^ 2, 10 ^ 2, 14 ^ 2, 22 ^ 2, 26 ^ 2, 15 ^ 2, 21 ^ 2} := by
        ext n
        constructor

        -- the forward direction
        .
          intro h
          simp at h
          obtain ⟨p, hp, q, hq, l, h, hn⟩ := h
          simp
          rw [h] at hn
          rw [show p ^ 2 * q ^ 2 = (p * q) ^ 2 by ring] at hn
          replace hn: p * q < 32 := by nlinarith
          replace hn: p * q ≤ 31 := by omega
          have lp: p ^ 2 ≤ 31 := by nlinarith
          replace lp: p < 6 := by nlinarith
          have o: p = 2 ∨ p = 3 ∨ p = 5 := by
            interval_cases p
            all_goals try omega
            all_goals norm_num at hp
          rcases o with o | o | o
          -- p = 2
          .
            simp [o] at *
            replace hn: q ≤ 15 := by omega
            interval_cases q
            all_goals norm_num at hq
            all_goals simp [h]
          -- p = 3
          .
            simp [o] at *
            replace hn: q ≤ 10 := by omega
            interval_cases q
            all_goals norm_num at hq
            all_goals simp [h]
          -- p = 5
          .
            simp [o] at *
            replace hn: q ≤ 6 := by omega
            interval_cases q
            all_goals norm_num at hq

        -- the backward direction
        .
          intro h
          simp at h
          rcases h with h | h | h | h | h | h | h
          all_goals simp [h]; clear h
          .
            use 2
            norm_num
            use 3
            norm_num
          .
            use 2
            norm_num
            use 5
            norm_num
          .
            use 2
            norm_num
            use 7
            norm_num
          .
            use 2
            norm_num
            use 11
            norm_num
          .
            use 2
            norm_num
            use 13
            norm_num
          .
            use 3
            norm_num
            use 5
            norm_num
          .
            use 3
            norm_num
            use 7
            norm_num


    -- we compute the cardinality
    rw [h_eq]
    simp [Set.encard]

