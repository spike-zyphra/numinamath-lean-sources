import Mathlib

theorem algebra_12017 :
    Set.ncard {y : ℤ | -3 * y ≥ y + 7 ∧ -2 * y ≤ 12 ∧ -4 * y ≥ 2 * y + 17} = 4 := by
  have h : {y : ℤ | -3 * y ≥ y + 7 ∧ -2 * y ≤ 12 ∧ -4 * y ≥ 2 * y + 17} = {-6, -5, -4, -3} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have h4 : y ≥ -6 := by 
        linarith 
      have h5 : y ≤ -3 := by 
        linarith 
      have : y = -6 ∨ y = -5 ∨ y = -4 ∨ y = -3 := by 
        omega 
      tauto 
    · rintro (rfl | rfl | rfl | rfl)
      · -- y = -6
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- y = -5
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- y = -4
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- y = -3
        exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { norm_num }