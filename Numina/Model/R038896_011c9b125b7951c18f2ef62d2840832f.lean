import Mathlib

theorem algebra_10210 : {x : ℕ | x > 0 ∧ 7 < x^2 + 10 ∧ 10 < x^2 + 7 ∧ 7 + 10 > x^2} = {2, 3, 4} := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume x is in the set, so it's a positive integer satisfying the inequalities
    rintro ⟨hx1, h1, h2, h3⟩
    have h4 : x ≤ 4 := by 
      nlinarith
    have h5 : x ≥ 2 := by 
      by_contra h
      push_neg at h
      have h6 : x < 2 := by 
        omega
      have h7 : x = 1 := by 
        omega
      rw [h7] at h1 h2 h3
      all_goals
        norm_num at h1 h2 h3
    have h8 : x = 2 ∨ x = 3 ∨ x = 4 := by
      interval_cases x <;> omega 
    tauto 
  · -- Show that {2, 3, 4} is contained in the set.
    rintro (rfl | rfl | rfl)
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num