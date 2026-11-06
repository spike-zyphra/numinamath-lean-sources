import Mathlib

theorem algebra_12930 : {m : ℕ | ∃ n : ℕ, 0 < m ∧ 0 < n ∧ m * n + 2 * m + 3 * n = 2019}.encard = 12 := by
  have h1 : {m : ℕ | ∃ n : ℕ, 0 < m ∧ 0 < n ∧ m * n + 2 * m + 3 * n = 2019} = 
          {2, 6, 12, 22, 24, 42, 72, 78, 132, 222, 402, 672} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First, prove if m in the set then m in the finite collection
      rintro ⟨n, hm, hn, h⟩
      have h1 : m ≤ 672 := by
        by_contra h1
        push_neg at h1
        have h2 : n ≤ 6 := by
          nlinarith
        interval_cases n <;> omega
      have h2 : n ≤ 672 := by
        by_contra h2
        push_neg at h2
        have h1 : m ≤ 6 := by
          nlinarith
        interval_cases m <;> omega
      interval_cases m <;> omega
    · -- Now the reverse direction
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- m = 2
        use 403
        all_goals norm_num
      · -- m = 6
        use 223
        all_goals norm_num
      · -- m = 12
        use 133
        all_goals norm_num
      · -- m = 22
        use 79
        all_goals norm_num
      · -- m = 24
        use 73
        all_goals norm_num
      · -- m = 42
        use 43
        all_goals norm_num
      · -- m = 72
        use 25
        all_goals norm_num
      · -- m = 78
        use 23
        all_goals norm_num
      · -- m = 132
        use 13
        all_goals norm_num
      · -- m = 222
        use 7
        all_goals norm_num
      · -- m = 402
        use 3
        all_goals norm_num
      · -- m = 672
        use 1
        all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }