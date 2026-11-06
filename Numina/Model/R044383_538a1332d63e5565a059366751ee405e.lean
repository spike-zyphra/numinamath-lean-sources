import Mathlib

theorem number_theory_7059 : ∑ᶠ n ∈ {n | n > 1 ∧ (Nat.digits n 2016).headI = 6}, n = 4879 := by
  have h1 : {n | n > 1 ∧ (Nat.digits n 2016).headI = 6} = 
          {10, 15, 30, 67, 134, 201, 335, 402, 670, 1005, 2010} := by
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n > 1 ∧ (Nat.digits n 2016).headI = 6
      intro h 
      rcases h with ⟨hn1, hln⟩
      have h2 : n ≤ 2016 := by 
        by_contra h
        push_neg at h 
        have h3 : n > 2016 := h 
        have h4 : (Nat.digits n 2016).headI = 2016 := by 
          simp [h3] 
        rw [h4] at hln 
        omega 
      interval_cases n <;> norm_num at hln ⊢ 
      <;> tauto
    · -- Show that these bases satisfy the condition 
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Base 10 
        constructor 
        · norm_num 
        · norm_num
      · -- Base 15 
        constructor 
        · norm_num 
        · norm_num 
      · -- Base 30 
        constructor 
        · norm_num 
        · norm_num
      · -- Base 67 
        constructor 
        · norm_num 
        · norm_num 
      · -- Base 134 
        constructor 
        · norm_num 
        · norm_num
      · -- Base 201 
        constructor 
        · norm_num 
        · norm_num 
      · -- Base 335 
        constructor 
        · norm_num 
        · norm_num 
      · -- Base 402 
        constructor 
        · norm_num 
        · norm_num 
      · -- Base 670 
        constructor 
        · norm_num 
        · norm_num 
      · -- Base 1005 
        constructor 
        · norm_num 
        · norm_num 
      · -- Base 2010 
        constructor 
        · norm_num 
        · norm_num 
  rw [h1] 
  rw [finsum_mem_eq_toFinset_sum]
  simp 
  <;> native_decide