import Mathlib

theorem number_theory_272250 :
    Set.ncard {n : ℕ | 0 < n ∧ n ≠ 1 ∧ 111 % n = 6} = 5 := by

  have h1 : {n : ℕ | 0 < n ∧ n ≠ 1 ∧ 111 % n = 6} = {7, 15, 21, 35, 105} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n > 0, n ≠ 1 and 111 % n = 6
      intro h
      rcases h with ⟨h1, h2, h3⟩
      have h4 : n ≤ 111 := by 
        by_contra h'
        push_neg at h'
        have h5 : 111 % n = 111 := by 
          rw [Nat.mod_eq_of_lt]
          all_goals linarith
        omega
      interval_cases n <;> norm_num at h3 <;> tauto

    · -- Show that these five numbers satisfy the constraints
      intro h
      rcases h with (rfl | rfl | rfl | rfl | rfl)
      · -- n = 7
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 15
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 21
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 35
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- n = 105
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num

  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]