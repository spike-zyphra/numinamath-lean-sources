import Mathlib

theorem algebra_10476: Set.ncard {x:ℤ | |x-2| ≤ (5.6:ℝ)} = 11 := by
  have h1 : {x : ℤ | |x - 2| ≤ (5.6 : ℝ)} = {-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume |x - 2| ≤ (5.6 : ℝ) prove x ∈ finite set
      intro h
      have h2 : abs ((x : ℝ) - (2 : ℝ)) ≤ (5.6 : ℝ) := by
        simpa using h
      have h3 : -(5.6 : ℝ) ≤ (x - 2 : ℝ) := by
        linarith [abs_le.mp h2]
      have h4 : (x - 2 : ℝ) ≤ (5.6 : ℝ) := by
        linarith [abs_le.mp h2]
      have h5 : x ≥ -3 := by 
        by_contra h5
        push_neg at h5
        have h6 : x ≤ -4 := by 
          omega
        have h7 : (x : ℝ) ≤ (-4 : ℝ) := by exact_mod_cast h6
        nlinarith
      have h6 : x ≤ 7 := by
        by_contra h6
        push_neg at h6
        have h7 : x ≥ 8 := by 
          omega
        have h8 : (x : ℝ) ≥ (8 : ℝ) := by 
          exact_mod_cast h7
        nlinarith
      interval_cases x <;> norm_num at h2 h3 h4 ⊢ <;> tauto
    · -- Assume x ∈ finite set prove |x - 2| ≤ (5.6 : ℝ)
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
      · norm_num [abs]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> native_decide