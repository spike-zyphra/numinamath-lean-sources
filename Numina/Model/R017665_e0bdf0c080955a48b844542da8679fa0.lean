import Mathlib

theorem number_theory_270215 : {n : ℕ | n > 0 ∧ 14 % n = 2}.encard = 4 := by
  have h : {n : ℕ | n > 0 ∧ 14 % n = 2} = {3, 4, 6, 12} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n in left side, prove n in right side
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : n ≤ 14 := by
        by_contra h
        push_neg at h
        have h4 : n > 14 := h
        have h5 : 14 % n = 14 := by
          rw [Nat.mod_eq_of_lt]
          all_goals
            omega
        omega
      interval_cases n <;> norm_num at h1 h2 ⊢ <;> tauto
    · -- Assume n in right side, prove n in left side
      rintro (rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton, Set.ncard_union_eq]
  <;> try { native_decide }