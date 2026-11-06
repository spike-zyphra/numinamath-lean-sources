import Mathlib

theorem number_theory_1349 : {x : ℤ | 5/3 < x ∧ x < 2 * Real.pi}.encard = 5 := by 
  have h1 : {x : ℤ | 5/3 < x ∧ x < 2 * Real.pi} = {2, 3, 4, 5, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x in left side
      intro h
      rcases h with ⟨h1, h2⟩
      have h16 : x ≥ 2 := by
        by_contra h
        push_neg at h
        have h4 : x ≤ 1 := by 
          omega 
        omega 
      have h17 : x ≤ 6 := by
        by_contra h
        push_neg at h 
        have h7 : x ≥ 7 := by 
          omega 
        have h8 : (x : ℝ) ≥ (7 : ℝ) := by exact_mod_cast h7
        have h9 : (x : ℝ) < (2 * Real.pi : ℝ) := by exact_mod_cast h2
        nlinarith [Real.pi_pos, Real.pi_gt_three, Real.pi_lt_31416]
      have h4 : x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by 
        omega 
      tauto 
    · -- Assume x in right side, prove in left 
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- x = 2 
        constructor 
        · norm_num 
        · -- Show 2 < 2 * Real.pi 
          have h1 : (2 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1 
      · -- x = 3 
        constructor 
        · norm_num 
        · -- Show 3 < 2 * Real.pi 
          have h1 : (3 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1 
      · -- x = 4 
        constructor 
        · norm_num 
        · -- Show 4 < 2 * Real.pi 
          have h1 : (4 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1 
      · -- x = 5 
        constructor 
        · norm_num 
        · -- Show 5 < 2 * Real.pi 
          have h1 : (5 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1 
      · -- x = 6 
        constructor 
        · norm_num 
        · -- Show 6 < 2 * Real.pi 
          have h1 : (6 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]