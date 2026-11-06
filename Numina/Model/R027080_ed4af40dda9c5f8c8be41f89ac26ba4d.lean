import Mathlib

theorem algebra_13323 : {x : ℤ | ∃ n : ℕ, x = n * 3 - 4 ∧ x ≤ 32}.encard = 13 := by 
  have h1 : {x : ℤ | ∃ n : ℕ, x = n * 3 - 4 ∧ x ≤ 32} = 
      {-4, -1, 2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 32} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      and_imp]
    constructor
    · -- First direction: {x : ℤ | ∃ n : ℕ, x = n * 3 - 4 ∧ x ≤ 32} ⊆ 
      rintro ⟨n, hn, h⟩
      have h2 : n ≤ 12 := by 
        omega
      interval_cases n <;> norm_num at hn h ⊢
      <;> tauto
    · -- Second direction: {-4, -1, 2, 5, 8, 11, 14, 17, 20, 23, 26, 29, 32} ⊆ {x : ℤ | ∃ n : ℕ, x = n * 3 - 4 ∧ x ≤ 32}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- -4
        use 0
        all_goals norm_num
      · -- -1
        use 1
        all_goals norm_num
      · -- 2
        use 2
        all_goals norm_num
      · -- 5
        use 3
        all_goals norm_num
      · -- 8
        use 4
        all_goals norm_num
      · -- 11
        use 5
        all_goals norm_num
      · -- 14
        use 6
        all_goals norm_num
      · -- 17
        use 7
        all_goals norm_num
      · -- 20
        use 8
        all_goals norm_num
      · -- 23
        use 9
        all_goals norm_num
      · -- 26
        use 10
        all_goals norm_num
      · -- 29
        use 11
        all_goals norm_num
      · -- 32
        use 12
        all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }
  <;> try { native_decide }