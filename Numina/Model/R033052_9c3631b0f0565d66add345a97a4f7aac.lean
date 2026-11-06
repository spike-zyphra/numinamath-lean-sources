import Mathlib

theorem inequalities_5359 :
    Set.ncard {x : ℕ | 0 < x ∧ x ^ 2 - 3 * x < 70} = 9 := by
  have h1 : {x : ℕ | 0 < x ∧ x ^ 2 - 3 * x < 70} = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in the left side, need to show x in the right side
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x ≤ 9 := by
        by_contra h4
        push_neg at h4
        have h4' : x ^ 2 ≥ 3 * x + 70 := by
          have h5 : x ≥ 10 := by omega
          nlinarith
        have h6 : x ^ 2 - 3 * x ≥ 70 := by
          omega
        omega
      interval_cases x <;> norm_num at h1 h2 ⊢
      all_goals try tauto
    · -- Assume x is in the right side, need to show x in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
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
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }