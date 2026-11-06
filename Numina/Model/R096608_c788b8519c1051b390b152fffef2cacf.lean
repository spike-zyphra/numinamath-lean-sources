import Mathlib

theorem number_theory_95283 :
Set.ncard {x : ℤ | 1000 ≤ x ∧ x < 2000 ∧ 15 ∣ x ∧ 20 ∣ x ∧ 25 ∣ x} = 3 := by 
  have h1 : {x : ℤ | 1000 ≤ x ∧ x < 2000 ∧ 15 ∣ x ∧ 20 ∣ x ∧ 25 ∣ x} = {1200, 1500, 1800} := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- Forward direction: if x is in the set, it's in {1200, 1500, 1800}
      intro h
      rcases h with ⟨h1, h2, h3, h4, h5⟩
      have h6 : x % 15 = 0 := by omega 
      have h7 : x % 20 = 0 := by omega 
      have h8 : x % 25 = 0 := by omega 
      have h9 : x % 300 = 0 := by 
        have h15 : x % 15 = 0 := h6 
        have h20 : x % 20 = 0 := h7 
        have h25 : x % 25 = 0 := h8 
        omega 
      omega 
    · -- Backward direction: if x is in {1200, 1500, 1800}, it's in the set
      rintro (rfl | rfl | rfl)
      · -- 1200: check it's in the set
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · -- 1500: check it's in the set
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · -- 1800: check it's in the set
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
  rw [h1]
  rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals norm_num