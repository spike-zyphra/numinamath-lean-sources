import Mathlib

theorem number_theory_13147 :
    ∑ᶠ n ∈ {x : ℕ | x ^ 3 < 2022 ∧ 2022 < 3 ^ x}, n = 57 := by 
  have : {x : ℕ | x ^ 3 < 2022 ∧ 2022 < 3 ^ x} = {7, 8, 9, 10, 11, 12} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x^3 < 2022 ∧ 2022 < 3^x
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x ≤ 12 := by
        by_contra h'
        push_neg at h'
        have h4 : x ≥ 13 := by omega
        have h5 : x ^ 3 ≥ 2023 := by
          have h6 : x ≥ 13 := by linarith
          have h7 : x ^ 3 ≥ 13 ^ 3 := by
            apply Nat.pow_le_pow_of_le_left 
            linarith 
          have h10 : 13 ^ 3 = 2197 := by norm_num 
          have h11 : x ^ 3 ≥ 2197 := by 
            linarith [h7, h10] 
          omega 
        linarith 
      have h4 : x ≥ 7 := by 
        by_contra h'
        push_neg at h'
        have h5 : x ≤ 6 := by omega 
        have h6 : 3 ^ x ≤ 729 := by
          have h7 : x ≤ 6 := by linarith 
          have h8 : 3 ^ x ≤ 3 ^ 6 := by 
            apply Nat.pow_le_pow_of_le_right 
            norm_num 
            linarith 
          have h9 : 3 ^ 6 = 729 := by norm_num 
          linarith 
        have h7 : 2022 < 3 ^ x := h2 
        linarith 
      interval_cases x <;> norm_num at h1 h2 ⊢ <;> tauto 
      <;> omega 
    · -- Assume x ∈ {7, 8, 9, 10, 11, 12}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 7
        constructor
        · norm_num 
        · norm_num 
      · -- x = 8
        constructor
        · norm_num 
        · norm_num 
      · -- x = 9
        constructor
        · norm_num 
        · norm_num 
      · -- x = 10
        constructor
        · norm_num 
        · norm_num 
      · -- x = 11
        constructor
        · norm_num 
        · norm_num 
      · -- x = 12
        constructor
        · norm_num 
        · norm_num 
  rw [this]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try { native_decide }
  <;> try { rfl }
  <;> try { omega }
  <;> try { native_decide }
  <;> try { omega }
  <;> try { native_decide }
  <;> try { omega }
  <;> try { native_decide }
  <;> try { omega }
  <;> try { native_decide }
  <;> try { omega }
  <;> try { native_decide }
  <;> try { omega }
  <;> try { native_decide }
  <;> try { omega }
  <;> try { native_decide }
  <;> try { omega }
  <;> try { native_decide }