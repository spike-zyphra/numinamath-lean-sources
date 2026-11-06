import Mathlib

theorem number_theory_260685 : {x : ℕ | x > 0 ∧ ⌊(x / 20 : ℝ)⌋ = ⌊(x / 17 : ℝ)⌋}.encard = 56 := by
  have h1 : {x : ℕ | x > 0 ∧ ⌊(x / 20 : ℝ)⌋ = ⌊(x / 17 : ℝ)⌋} = Finset.toSet (Finset.Icc 1 16 ∪ Finset.Icc 20 33 ∪ Finset.Icc 40 50 ∪ Finset.Icc 60 67 ∪ Finset.Icc 80 84 ∪ Finset.Icc 100 101) := by 
    ext x
    simp
    constructor
    · -- Assume x > 0 and ⌊(x / 20 : ℝ)⌋ = ⌊(x / 17 : ℝ)⌋
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h2 : (x : ℝ) > (0 : ℝ) := by exact_mod_cast hx1
      have h20 : ⌊((x : ℝ) / 20)⌋ = ⌊((x : ℝ) / 17)⌋ := by exact_mod_cast hx2
      have h3 : x ≤ 121 := by
        by_contra h4
        push_neg at h4
        have h4' : x ≥ 122 := by linarith
        have h5 : ⌊((x : ℝ) / 20)⌋ ≥ 6 := by
          have h6 : (x : ℝ) / 20 ≥ (122 : ℝ) / 20 := by
            have h7 : (x : ℝ) ≥ (122 : ℝ) := by exact_mod_cast h4'
            linarith
          have h7 : ⌊((x : ℝ) / 20)⌋ ≥ ⌊((122 : ℝ) / 20)⌋ := by
            apply Int.floor_le_floor
            linarith [h6]
          norm_num [Int.floor_eq_iff] at h7 ⊢
          exact_mod_cast h7
        have h6 : ⌊((x : ℝ) / 17)⌋ ≥ 7 := by
          have h7 : (x : ℝ) / 17 ≥ (122 : ℝ) / 17 := by
            have h8 : (x : ℝ) ≥ (122 : ℝ) := by exact_mod_cast h4'
            linarith
          have h8 : ⌊((x : ℝ) / 17)⌋ ≥ ⌊((122 : ℝ) / 17)⌋ := by
            apply Int.floor_le_floor
            linarith [h7]
          norm_num [Int.floor_eq_iff] at h8 ⊢
          exact_mod_cast h8
        have h7 : ⌊((x : ℝ) / 20)⌋ < ⌊((x : ℝ) / 17)⌋ := by
          have h8 : ⌊((x : ℝ) / 20)⌋ < ⌊((x : ℝ) / 17)⌋ := by
            have h9 : ⌊((x : ℝ) / 20)⌋ < ⌊((x : ℝ) / 17)⌋ := by
              have h10 : (x : ℝ) / 17 ≥ (x : ℝ) / 20 + (1 : ℝ) := by
                have h11 : (x : ℝ) ≥ (122 : ℝ) := by exact_mod_cast h4'
                nlinarith
              have h11 : ⌊((x : ℝ) / 17)⌋ ≥ ⌊((x : ℝ) / 20)⌋ + 1 := by
                have h12 : (x : ℝ) / 17 ≥ (x : ℝ) / 20 + (1 : ℝ) := by
                  linarith
                have h13 : ⌊((x : ℝ) / 17)⌋ ≥ ⌊((x : ℝ) / 20 + (1 : ℝ))⌋ := by
                  apply Int.floor_le_floor
                  linarith [h12]
                rw [Int.floor_add_one] at h13
                all_goals omega
              omega
            linarith
          omega
        omega
      interval_cases x <;> norm_num at hx1 hx2 ⊢ <;> norm_num [Int.floor_eq_iff] at hx2 ⊢ <;> tauto 
    · -- Assume x in the right side
      rintro (h | h | h | h | h | h)
      · -- Assume x ∈ [1, 16]
        rcases h with ⟨hx1, hx2⟩
        constructor
        · -- Show x > 0
          linarith 
        · -- Show ⌊x / 20⌋ = ⌊x / 17⌋
          have h5 : x ≤ 16 := by linarith 
          interval_cases x <;> norm_num 
          all_goals norm_num [Int.floor_eq_iff] at *
      · -- Assume x ∈ [20, 33]
        rcases h with ⟨hx1, hx2⟩
        constructor
        · -- Show x > 0
          linarith 
        · -- Show ⌊x / 20⌋ = ⌊x / 17⌋
          have h5 : x ≤ 33 := by linarith 
          interval_cases x <;> norm_num 
          all_goals norm_num [Int.floor_eq_iff] at *
      · -- Assume x ∈ [40, 50]
        rcases h with ⟨hx1, hx2⟩
        constructor
        · -- Show x > 0
          linarith 
        · -- Show ⌊x / 20⌋ = ⌊x / 17⌋
          have h5 : x ≤ 50 := by linarith 
          interval_cases x <;> norm_num 
          all_goals norm_num [Int.floor_eq_iff] at *
      · -- Assume x ∈ [60, 67]
        rcases h with ⟨hx1, hx2⟩
        constructor
        · -- Show x > 0
          linarith 
        · -- Show ⌊x / 20⌋ = ⌊x / 17⌋
          have h5 : x ≤ 67 := by linarith 
          interval_cases x <;> norm_num 
          all_goals norm_num [Int.floor_eq_iff] at *
      · -- Assume x ∈ [80, 84]
        rcases h with ⟨hx1, hx2⟩
        constructor
        · -- Show x > 0
          linarith 
        · -- Show ⌊x / 20⌋ = ⌊x / 17⌋
          have h5 : x ≤ 84 := by linarith 
          interval_cases x <;> norm_num 
          all_goals norm_num [Int.floor_eq_iff] at *
      · -- Assume x ∈ [100, 101]
        rcases h with ⟨hx1, hx2⟩
        constructor
        · -- Show x > 0
          linarith 
        · -- Show ⌊x / 20⌋ = ⌊x / 17⌋
          have h5 : x ≤ 101 := by linarith 
          interval_cases x <;> norm_num 
          all_goals norm_num [Int.floor_eq_iff] at *
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide