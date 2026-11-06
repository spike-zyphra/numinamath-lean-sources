import Mathlib

theorem number_theory_56673 :
    Set.ncard {m | 2023 % m = 23} = 12 := by 
  have h1 : {m | 2023 % m = 23} = {25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 1000, 2000} := by
    ext m 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward direction: if 2023 % m = 23, then m ∈ {25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 1000, 2000}
      intro h
      have h2 : m ≤ 2023 := by 
        by_contra h'
        push_neg at h'
        have h3 : 2023 % m = 2023 := by 
          rw [Nat.mod_eq_of_lt]
          omega
          all_goals omega 
        rw [h3] at h
        omega 
      interval_cases m <;> norm_num at h ⊢ <;> tauto 
    · -- Backward direction: if m ∈ {25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 1000, 2000}, then 2023 % m = 23
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
      · norm_num 
  rw [h1]
  norm_num
  <;> try native_decide