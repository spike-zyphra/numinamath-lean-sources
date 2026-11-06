import Mathlib

theorem algebra_19883 :
    {x : ℕ | x > 0 ∧ 120 % x = 0 ∧ 40 % x = 0}.encard = 8 := by 
  have h1 : {x : ℕ | x > 0 ∧ 120 % x = 0 ∧ 40 % x = 0} = {1, 2, 4, 5, 8, 10, 20, 40} := by
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the set
      intro h 
      rcases h with ⟨hn_pos, hn_120, hn_40⟩
      have h1 : n ≤ 40 := by 
        by_contra h
        push_neg at h 
        have h4 : 40 % n = 40 := by 
          rw [Nat.mod_eq_of_lt] 
          all_goals linarith 
        omega 
      interval_cases n <;> norm_num at *
    · -- Assume n is in the explicit set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- n = 2
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- n = 4
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- n = 5
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- n = 8
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- n = 10
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- n = 20
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- n = 40
        exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]