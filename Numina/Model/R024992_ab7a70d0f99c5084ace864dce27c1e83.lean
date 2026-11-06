import Mathlib

theorem number_theory_246772 :
    {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ ⌊(1.9 * x : ℝ)⌋ + ⌊(8.8 * y : ℝ)⌋ = 36}.ncard = 3 := by

  have h1 : {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ ⌊(1.9 * x : ℝ)⌋ + ⌊(8.8 * y : ℝ)⌋ = 36} = {(15, 1), (10, 2), (1, 4)} := by
    ext ⟨x, y⟩
    simp
    constructor
    · rintro ⟨hx, hy, heq⟩
      have h2 : y ≤ 4 := by
        by_contra h
        push_neg at h
        have h3 : ⌊(8.8 * (y : ℝ) )⌋ ≥ 37 := by
          have h4 : (8.8 * (y : ℝ) ) ≥ (37 : ℝ) := by
            have h5 : (y : ℝ) ≥ (5 : ℝ) := by
              exact_mod_cast (show y ≥ 5 by omega)
            nlinarith
          have h6 : ⌊(8.8 * (y : ℝ))⌋ ≥ ⌊ (37 : ℝ) ⌋ := by
            apply Int.floor_le_floor
            linarith
          norm_num at h6 ⊢
          linarith
        have h5 : ⌊(1.9 * (x : ℝ))⌋ ≥ 0 := by
          have h8 : (1.9 * (x : ℝ) ) ≥ (0 : ℝ) := by
            have h9 : (x : ℝ) ≥ (1 : ℝ) := by
              exact_mod_cast (show x ≥ 1 by omega)
            nlinarith
          have h10 : ⌊(1.9 * (x : ℝ) )⌋ ≥ ⌊ (0 : ℝ) ⌋ := by
            apply Int.floor_le_floor
            linarith
          norm_num at h10 ⊢
          linarith
        omega
      have h3 : x ≤ 19 := by
        by_contra h
        push_neg at h
        have h4 : ⌊(1.9 * (x : ℝ) )⌋ ≥ 37 := by
          have h5 : (1.9 * (x : ℝ) ) ≥ (37 : ℝ) := by
            have h6 : (x : ℝ) ≥ (20 : ℝ) := by
              exact_mod_cast (show x ≥ 20 by omega)
            nlinarith
          have h7 : ⌊(1.9 * (x : ℝ))⌋ ≥ ⌊ (37 : ℝ) ⌋ := by
            apply Int.floor_le_floor
            linarith
          norm_num at h7 ⊢
          linarith
        have h5 : ⌊(8.8 * (y : ℝ) )⌋ ≥ 0 := by
          have h8 : (8.8 * (y : ℝ) ) ≥ (0 : ℝ) := by
            have h9 : (y : ℝ) ≥ (1 : ℝ) := by
              exact_mod_cast (show y ≥ 1 by omega)
            nlinarith
          have h10 : ⌊(8.8 * (y : ℝ) )⌋ ≥ ⌊ (0 : ℝ) ⌋ := by
            apply Int.floor_le_floor
            linarith
          norm_num at h10 ⊢
          linarith
        omega
      interval_cases y <;> interval_cases x <;> norm_num at heq ⊢ <;> tauto
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · -- Check that (15, 1) is a solution
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Int.floor_eq_iff]
      · -- Check that (10, 2) is a solution
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Int.floor_eq_iff]
      · -- Check that (1, 4) is a solution
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num [Int.floor_eq_iff]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }