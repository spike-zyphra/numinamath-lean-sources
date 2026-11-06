import Mathlib

theorem number_theory_125909 : {n | n.Prime ∧ n ≤ 36}.encard = 11 := by
  have h1 : {n | n.Prime ∧ n ≤ 36} = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · intro h
      rcases h with ⟨hx1, hx2⟩
      interval_cases x <;> norm_num at hx1 hx2 ⊢ <;> tauto
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try native_decide