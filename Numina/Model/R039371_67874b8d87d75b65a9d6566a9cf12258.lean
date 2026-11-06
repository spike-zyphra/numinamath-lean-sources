import Mathlib

theorem number_theory_199538 :
    {n | 38 ∣ n ∧ n = 3624 ∨ n = 36024 ∨ n = 360924 ∨ n = 3609924 ∨ n = 36099924 ∨ n = 360999924 ∨ n = 3609999924}.encard = 6 := by 
  have h1 : {n | 38 ∣ n ∧ n = 3624 ∨ n = 36024 ∨ n = 360924 ∨ n = 3609924 ∨ n = 36099924 ∨ n = 360999924 ∨ n = 3609999924} = {36024, 360924, 3609924, 36099924, 360999924, 3609999924} := by 
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor 
    · -- Assume h : n in left side
      rintro (h' | h' | h' | h' | h' | h' | h')
      · -- First case: 38 ∣ n ∧ n = 3624
        exfalso 
        have h10 : n = 3624 := h'.2
        have h11 : 38 ∣ n := h'.1
        rw [h10] at h11 
        norm_num at h11
      · -- n = 36024
        simp [h']
      · -- n = 360924
        simp [h']
      · -- n = 3609924
        simp [h']
      · -- n = 36099924
        simp [h']
      · -- n = 360999924
        simp [h']
      · -- n = 3609999924
        simp [h']
    · -- Assume n ∈ right side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- 36024
        norm_num 
      · -- 360924
        norm_num 
      · -- 3609924
        norm_num 
      · -- 36099924
        norm_num 
      · -- 360999924
        norm_num 
      · -- 3609999924
        norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]