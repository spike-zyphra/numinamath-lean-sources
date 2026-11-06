import Mathlib

theorem inequalities_13316 : {x : ℤ | -4 ≤ (x - 7)^2 / 3 + 5 ∧ (x - 7)^2 / 3 + 5 ≤ 14}.ncard = 11 := by
  have h1 : {x : ℤ | -4 ≤ (x - 7)^2 / 3 + 5 ∧ (x - 7)^2 / 3 + 5 ≤ 14} = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: the inequalities imply the explicit set.
      rintro ⟨h1, h2⟩
      have h3 : x ≤ 12 := by
        by_contra h 
        push_neg at h 
        have h4 : x > 12 := by linarith 
        have h5 : (x - 7) ^ 2 / 3 ≥ 10 := by 
          have h6 : x > 12 := h4 
          have h7 : x ≥ 13 := by omega 
          have h8 : (x - 7) ^ 2 ≥ 30 := by
            have h9 : x - 7 ≥ 6 := by omega 
            nlinarith
          have h9 : (x - 7) ^ 2 / 3 ≥ 10 := by 
            omega 
          linarith 
        have h6 : (x - 7) ^ 2 / 3 + 5 ≥ 14 + 1 := by 
          omega 
        nlinarith
      have h4 : x ≥ 2 := by
        by_contra h 
        push_neg at h 
        have h7 : x ≤ 1 := by omega 
        have h8 : (x - 7) ^ 2 ≥ 36 := by 
          have h9 : x ≤ 1 := by omega 
          nlinarith
        have h9 : (x - 7) ^ 2 / 3 ≥ 12 := by 
          have h3 : (x - 7) ^ 2 ≥ 36 := h8
          have h4 : (x - 7) ^ 2 / 3 ≥ 12 := by
            omega 
          linarith 
        have h20 : (x - 7) ^ 2 / 3 + 5 ≥ 17 := by 
          omega 
        omega
      interval_cases x <;> omega 
    · -- Second part of equivalence
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 2
        constructor <;> omega 
      · -- x = 3 
        constructor <;> omega 
      · -- x = 4 
        constructor <;> omega 
      · -- x = 5 
        constructor <;> omega 
      · -- x = 6 
        constructor <;> omega 
      · -- x = 7 
        constructor <;> omega 
      · -- x = 8 
        constructor <;> omega 
      · -- x = 9 
        constructor <;> omega 
      · -- x = 10 
        constructor <;> omega 
      · -- x = 11 
        constructor <;> omega 
      · -- x = 12 
        constructor <;> omega 
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide