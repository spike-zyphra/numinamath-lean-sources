import Mathlib

theorem number_theory_318680 :
    {(x, y) : ℕ × ℕ | ⌊(2.018 * x : ℝ)⌋ + ⌊(5.13 * y : ℝ)⌋ = 24}.ncard = 3 := by
  have h1 : {(x, y) : ℕ × ℕ | ⌊(2.018 * x : ℝ)⌋ + ⌊(5.13 * y : ℝ)⌋ = 24} = {(2, 4), (7, 2), (12, 0)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · -- First, show that if $(x, y)$ is a solution, then it's in the finite set.
      rintro h
      have h2 : x ≤ 12 := by
        by_contra h2
        push_neg at h2
        have h3 : ⌊(2.018 * (x : ℝ) )⌋ ≥ 25 := by
          have h4 : (2.018 * (x : ℝ) ) ≥ (25.18 : ℝ) := by
            have h5 : (x : ℝ) ≥ (13 : ℝ) := by
              have h6 : x ≥ 13 := by omega
              exact_mod_cast h6
            nlinarith
          have h7 : ⌊(2.018 * (x : ℝ) )⌋ ≥ ⌊(25.18 : ℝ)⌋ := by 
            apply Int.floor_le_floor
            all_goals linarith
          have h8 : ⌊(25.18 : ℝ)⌋ = 25 := by 
            norm_num
          omega
        have h41 : ⌊(5.13 * (y : ℝ) )⌋ ≥ 0 := by
          have h5 : (5.13 * (y : ℝ) ) ≥ (0 : ℝ) := by
            have h6 : (y : ℝ) ≥ (0 : ℝ) := by exact_mod_cast (show (0 : ℕ) ≤ y by omega)
            nlinarith
          have h61 : ⌊(5.13 * (y : ℝ) )⌋ ≥ ⌊(0 : ℝ)⌋ := by 
            apply Int.floor_le_floor
            all_goals linarith
          have h7 : ⌊(0 : ℝ)⌋ = 0 := by 
            norm_num
          omega
        omega
      have h3 : y ≤ 4 := by
        by_contra h3
        push_neg at h3
        have h4 : ⌊(5.13 * (y : ℝ) )⌋ ≥ 25 := by
          have h5 : (5.13 * (y : ℝ) ) ≥ (25.65 : ℝ) := by
            have h6 : (y : ℝ) ≥ (5 : ℝ) := by
              have h7 : y ≥ 5 := by omega
              exact_mod_cast h7
            nlinarith
          have h7 : ⌊(5.13 * (y : ℝ) )⌋ ≥ ⌊(25.65 : ℝ)⌋ := by 
            apply Int.floor_le_floor
            all_goals linarith
          have h8 : ⌊(25.65 : ℝ)⌋ = 25 := by 
            norm_num
          omega
        have h41 : ⌊(2.018 * (x : ℝ) )⌋ ≥ 0 := by
          have h5 : (2.018 * (x : ℝ) ) ≥ (0 : ℝ) := by
            have h6 : (x : ℝ) ≥ (0 : ℝ) := by exact_mod_cast (show (0 : ℕ) ≤ x by omega)
            nlinarith
          have h61 : ⌊(2.018 * (x : ℝ) )⌋ ≥ ⌊(0 : ℝ)⌋ := by 
            apply Int.floor_le_floor
            all_goals linarith
          have h7 : ⌊(0 : ℝ)⌋ = 0 := by 
            norm_num
          omega
        omega
      interval_cases x <;> interval_cases y
      <;> norm_num at h ⊢
      <;> tauto
    · -- Show that each pair in the finite set is a solution.
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
  rw [h1] at *
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }