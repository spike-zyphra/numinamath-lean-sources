import Mathlib

theorem number_theory_278651 : {x : ℕ | 10 ≤ x ∧ x < 20 ∧ Nat.Prime x}.encard = 4 := by 
  have h1 : {x : ℕ | 10 ≤ x ∧ x < 20 ∧ Nat.Prime x} = {11, 13, 17, 19} := by
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases h with ⟨h1, h2, h3⟩
      interval_cases x <;> tauto 
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨by norm_num, by norm_num, by norm_num⟩ 
      · exact ⟨by norm_num, by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num, by norm_num⟩
      · exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }