import Mathlib

theorem number_theory_22750 :
    {x | x > 0 ∧ x ∣ 4000 ∧ 100 ∣ x}.encard = 8 := by 
  have h1 : {x | x > 0 ∧ x ∣ 4000 ∧ 100 ∣ x} = {100, 200, 400, 500, 800, 1000, 2000, 4000} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is in the left side, prove in the right side
      intro h
      rcases h with ⟨h_pos, h_div, h_100⟩
      have h4 : n ≤ 4000 := by 
        exact Nat.le_of_dvd (by norm_num) h_div
      interval_cases n <;> norm_num at *
      <;> omega 
    · -- Assume n is in the right side, prove in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
      · constructor
        · norm_num 
        constructor
        · norm_num 
        · norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }