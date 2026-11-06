import Mathlib

theorem number_theory_195600 :
    Set.ncard {n : ℕ | 0 < n ∧ n < 100 ∧ ∃ k, n = k^2 ∧ ∃ m, n = m^3} = 2 := by
  have h1 : {n : ℕ | 0 < n ∧ n < 100 ∧ ∃ k, n = k^2 ∧ ∃ m, n = m^3} = {1, 64} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n in the original set, prove it's in {1, 64}
      rintro ⟨hn_pos, hn_lt_100, k, rfl, m, h4⟩
      have h5 : k < 10 := by
        by_contra h
        push_neg at h
        have h6 : k ^ 2 ≥ 100 := by
          nlinarith
        linarith
      have h6 : m < 5 := by
        by_contra h
        push_neg at h
        have h7 : m ^ 3 ≥ 125 := by
          have h5 : m ≥ 5 := by linarith
          have h6 : m ^ 3 ≥ 5 ^ 3 := by
            apply Nat.pow_le_pow_of_le_left
            omega
            all_goals omega
          linarith
        nlinarith
      interval_cases k <;> try { 
        interval_cases m <;> omega 
      }
    · -- Assume n in {1, 64}, prove it's in the original set
      rintro (rfl | rfl)
      · -- n = 1
        constructor
        · norm_num
        constructor
        · norm_num
        · -- witness
          use 1
          constructor
          · -- Show n = k ^ 2
            norm_num
            all_goals norm_num
          · -- witness
            use 1
            all_goals norm_num
      · -- n = 64
        constructor
        · norm_num
        constructor
        · norm_num
        · -- witness
          use 8
          constructor
          · -- Show n = k ^ 2
            norm_num
          · -- witness
            use 4
            all_goals norm_num
  rw [h1]
  norm_num [Set.ncard_pair]