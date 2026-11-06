import Mathlib

theorem number_theory_175607 :
    {a : ℕ | 0 < a ∧ 2216 % a = 29}.encard = 4 := by
  have h1 : {a : ℕ | 0 < a ∧ 2216 % a = 29} = {81, 243, 729, 2187} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume a is in the set {a | 0 < a ∧ 2216 % a = 29} 
      intro h
      rcases h with ⟨ha_pos, hrem⟩
      have h1 : a ≤ 2216 := by
        by_contra h
        push_neg at h
        have h2 : 2216 % a = 2216 := by
          rw [Nat.mod_eq_of_lt]
          all_goals linarith
        omega
      interval_cases a <;> norm_num at hrem ⊢ <;> tauto
    · -- Assume a is in the set {81, 243, 729, 2187}
      rintro (rfl | rfl | rfl | rfl)
      · constructor
        · norm_num -- a is positive
        · norm_num -- 2216 % 81 = 29
      · constructor
        · norm_num -- a is positive
        · norm_num -- 2216 % 243 = 29
      · constructor
        · norm_num -- a is positive
        · norm_num -- 2216 % 729 = 29
      · constructor
        · norm_num -- a is positive
        · norm_num -- 2216 % 2187 = 29
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try native_decide
  <;> try trivial