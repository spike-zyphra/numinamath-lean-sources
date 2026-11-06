import Mathlib

theorem number_theory_4341 :
    ∑ᶠ n ∈ {n : ℤ | round ((8 * n / 23 : ℝ)) = 36}, n = 103 + 104 := by
  have h1 : {n : ℤ | round ((8 * n / 23 : ℝ)) = 36} = {103, 104} := by 
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n ∈ {n : ℤ | round ((8 * n / 23 : ℝ)) = 36}
      intro h
      have eq1 : ⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ = 36 := by 
        norm_num [round_eq] at h ⊢
        all_goals exact_mod_cast h 
      have h5 : (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) ≥ (36 : ℝ) := by
        have h6 : ⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ = 36 := eq1
        have h8 : (36 : ℝ) ≤ (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) := by 
          have h9 : ⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ ≤ (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) := by
            exact Int.floor_le (8 * (n : ℝ) / 23 + 1 / 2 : ℝ)
          have h11 : ⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ = (36 : ℤ) := by
            exact_mod_cast h6
          have h12 : (⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ : ℝ) = (36 : ℝ) := by
            exact_mod_cast h11
          linarith
        linarith
      have h6 : (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) < (37 : ℝ) := by
        have h7 : ⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ = 36 := eq1
        have h8 : (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) < (⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ + 1 : ℝ) := by 
          exact Int.lt_floor_add_one (8 * (n : ℝ) / 23 + 1 / 2 : ℝ)
        have h9 : ⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ = (36 : ℤ) := by
          exact_mod_cast h7
        have h11 : (⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ + 1 : ℝ) = (37 : ℝ) := by
          have h12 : ⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ = (36 : ℤ) := h9
          have h13 : (⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ : ℤ) = 36 := by exact_mod_cast h12
          have h14 : ⌊(8 * (n : ℝ) / 23 + 1 / 2 : ℝ)⌋ + 1 = 37 := by
            omega
          exact_mod_cast h14
        linarith
      have h4 : n ≥ 103 := by
        by_contra h
        push_neg at h
        have h5' : n ≤ 102 := by omega
        have h8 : (n : ℝ) ≤ (102 : ℝ) := by exact_mod_cast h5'
        -- h5_1 is (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) ≥ (36 : ℝ)
        have h11 : (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) ≥ (36 : ℝ) := h5
        nlinarith 
      have h5 : n ≤ 104 := by
        by_contra h
        push_neg at h
        have h6' : n ≥ 105 := by omega
        have h8 : (n : ℝ) ≥ (105 : ℝ) := by exact_mod_cast h6'
        -- h6_1 is (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) < (37 : ℝ)
        have h6_1 : (8 * (n : ℝ) / 23 + 1 / 2 : ℝ) < (37 : ℝ) := h6
        nlinarith
      have h8 : n = 103 ∨ n = 104 := by
        omega 
      tauto
    · -- Assume n ∈ {103, 104}
      rintro (rfl | rfl)
      · -- Check n = 103
        norm_num [round_eq]
        <;> norm_num 
      · -- Check n = 104
        norm_num [round_eq]
        <;> norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num
  all_goals linarith