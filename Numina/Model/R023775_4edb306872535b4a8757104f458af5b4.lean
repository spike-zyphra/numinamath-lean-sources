import Mathlib

theorem number_theory_126837 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ ⌊(3.11 * x : ℝ)⌋ + ⌊(2.03 * y : ℝ)⌋ = 30}.ncard = 4 := by
  have h1 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ ⌊(3.11 * x : ℝ)⌋ + ⌊(2.03 * y : ℝ)⌋ = 30} = {(2, 12), (4, 9), (6, 6), (8, 3)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- Show that if $(x,y)$ is in the set, then it's one of the pairs
      rintro ⟨hx, hy, heq⟩
      have h2 : x ≤ 10 := by
        by_contra h
        push_neg at h
        have h3 : ⌊(3.11 * x : ℝ)⌋ ≥ 32 := by
          have h4 : (3.11 * x : ℝ) ≥ (32 : ℝ) := by
            have h5 : x ≥ 11 := by omega
            have h6 : (x : ℝ) ≥ (11 : ℝ) := by exact_mod_cast h5
            nlinarith
          have h7 : ⌊(3.11 * x : ℝ)⌋ ≥ ⌊(32 : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          norm_num at h7 ⊢
          omega
        have h30 : ⌊(3.11 * x : ℝ)⌋ + ⌊(2.03 * y : ℝ)⌋ ≥ 32 := by
          have h1 : ⌊(3.11 * x : ℝ)⌋ ≥ 32 := h3
          have h2 : ⌊(2.03 * y : ℝ)⌋ ≥ 0 := by
            have h11 : (2.03 * y : ℝ) ≥ 0 := by
              positivity
            have h22 : ⌊(2.03 * y : ℝ)⌋ ≥ ⌊(0 : ℝ)⌋ := by
              apply Int.floor_le_floor 
              linarith
            norm_num at h22 ⊢ 
            omega
          omega
        linarith
      have h3 : y ≤ 15 := by
        by_contra h
        push_neg at h
        have h8 : ⌊(2.03 * y : ℝ)⌋ ≥ 32 := by
          have h7 : (2.03 * y : ℝ) ≥ (32 : ℝ) := by
            have h5 : y ≥ 16 := by omega
            have h6 : (y : ℝ) ≥ (16 : ℝ) := by exact_mod_cast h5
            nlinarith
          have h9 : ⌊(2.03 * y : ℝ)⌋ ≥ ⌊(32 : ℝ)⌋ := by
            apply Int.floor_le_floor
            linarith
          norm_num at h9 ⊢
          omega
        have h30 : ⌊(3.11 * x : ℝ)⌋ + ⌊(2.03 * y : ℝ)⌋ ≥ 32 := by
          have h1 : ⌊(3.11 * x : ℝ)⌋ ≥ 0 := by
            have h11 : (3.11 * x : ℝ) ≥ 0 := by
              positivity
            have h22 : ⌊(3.11 * x : ℝ)⌋ ≥ ⌊(0 : ℝ)⌋ := by
              apply Int.floor_le_floor 
              linarith
            norm_num at h22 ⊢ 
            omega
          have h2 : ⌊(2.03 * y : ℝ)⌋ ≥ 32 := h8
          omega
        linarith
      interval_cases x <;> interval_cases y <;> norm_num at heq hx hy ⊢ <;> tauto
    · -- Show that these pairs satisfy the equation
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
  have h2 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ ⌊(3.11 * x : ℝ)⌋ + ⌊(2.03 * y : ℝ)⌋ = 30}.ncard = 4 := by
    rw [h1]
    rw [Set.ncard_eq_toFinset_card']
    simp [Set.toFinset]
    <;> try { native_decide }
  exact h2