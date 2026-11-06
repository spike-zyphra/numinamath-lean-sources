import Mathlib

theorem inequalities_5830 :
    Set.ncard {x : ℕ | 0 < x ∧ 9 * x - 56 < 75} = 14 := by 
  have h1 : {x : ℕ | 0 < x ∧ 9 * x - 56 < 75} = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if x is in the set, then x ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14}
      intro h
      rcases h with ⟨hx1, hx2⟩
      omega
    · -- Second direction: if x ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14}, then x is in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- 1
        constructor
        · norm_num 
        · norm_num
      · -- 2
        constructor
        · norm_num 
        · norm_num
      · -- 3
        constructor
        · norm_num 
        · norm_num
      · -- 4
        constructor
        · norm_num 
        · norm_num
      · -- 5
        constructor
        · norm_num 
        · norm_num
      · -- 6
        constructor
        · norm_num 
        · norm_num
      · -- 7
        constructor
        · norm_num 
        · norm_num
      · -- 8
        constructor
        · norm_num 
        · norm_num
      · -- 9
        constructor
        · norm_num 
        · norm_num
      · -- 10
        constructor
        · norm_num 
        · norm_num
      · -- 11
        constructor
        · norm_num 
        · norm_num
      · -- 12
        constructor
        · norm_num 
        · norm_num
      · -- 13
        constructor
        · norm_num 
        · norm_num
      · -- 14
        constructor
        · norm_num 
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }