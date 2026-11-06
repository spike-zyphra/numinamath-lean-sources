import Mathlib

theorem number_theory_22959 :
    Set.ncard {b | b > 1 ∧ (Nat.digits b 2013).headI = 3} = 13 := by
  have h1 : {b | b > 1 ∧ (Nat.digits b 2013).headI = 3} = {5, 6, 10, 15, 30, 67, 134, 201, 335, 402, 670, 1005, 2010} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h : b > 1 ∧ (Nat.digits b 2013).headI = 3
      intro h
      rcases h with ⟨hb1, h1⟩
      have h2 : b ≤ 2013 := by
        by_contra h
        push_neg at h
        have h3 : (Nat.digits b 2013).headI = 2013 := by
          simp [h]
          <;> omega
        rw [h3] at h1
        omega
      interval_cases b <;> norm_num at h1 ⊢ <;> tauto
    · -- Assume b ∈ {5, 6, 10, 15, 30, 67, 134, 201, 335, 402, 670, 1005, 2010}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
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