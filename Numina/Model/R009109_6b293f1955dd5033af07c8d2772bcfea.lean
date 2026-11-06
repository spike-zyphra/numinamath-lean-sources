import Mathlib

theorem number_theory_12461 : {x | x ≠ 0 ∧ 47 % x = 5}.encard = 5 := by
  have h1 : {x | x ≠ 0 ∧ 47 % x = 5} = {6, 7, 14, 21, 42} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h : (x ≠ 0) ∧ (47 % x = 5)
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h2 : x ≤ 47 := by
        by_contra h3
        push_neg at h3
        have h4 : 47 % x = 47 := by
          rw [Nat.mod_eq_of_lt]
          all_goals omega
        omega
      interval_cases x <;> tauto
    · -- Assume h : (x = 6 ∨ x = 7 ∨ x = 14 ∨ x = 21 ∨ x = 42)
      rintro (rfl | rfl | rfl | rfl | rfl)
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
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  norm_num [Set.ncard]
  all_goals try { tauto }
  all_goals try { norm_num }
  all_goals try { native_decide }
  all_goals try { tauto }