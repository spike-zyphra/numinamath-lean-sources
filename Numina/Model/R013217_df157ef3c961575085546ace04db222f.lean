import Mathlib

theorem number_theory_94567 : Set.ncard {x : ℤ | x > 0 ∧ x < 2 * Real.pi ∧ x > 5 / 3} = 5 := by
  have h1 : {x : ℤ | x > 0 ∧ x < 2 * Real.pi ∧ x > 5 / 3} = {2, 3, 4, 5, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x in {x : ℤ | x > 0 ∧ x < 2 * Real.pi ∧ x > 5 / 3}, prove x in {2, 3, 4, 5, 6}
      intro h
      rcases h with ⟨h1, h2, h3⟩
      have h4 : x ≥ 2 := by
        by_contra h
        push_neg at h
        have h5 : x ≤ 1 := by omega
        have h8 : x ≤ 1 := by linarith
        have h9 : x > 1 := by
          by_contra h
          push_neg at h
          -- h : x ≤ 1
          have h10 : x ≤ 1 := by omega
          have h11 : (x : ℝ) ≤ (1 : ℝ) := by exact_mod_cast h10
          norm_num at h3
          nlinarith
        linarith
      have h5 : x ≤ 6 := by
        by_contra h
        push_neg at h
        have h8 : x ≥ 7 := by omega
        have h9 : (x : ℝ) ≥ (7 : ℝ) := by exact_mod_cast h8
        have : (2 * Real.pi : ℝ) < (7 : ℝ) := by 
          nlinarith [Real.pi_lt_31416]
        linarith
      interval_cases x <;> norm_num at h1 h2 h3 ⊢
      <;> tauto
    · -- Assume x in {2, 3, 4, 5, 6}, prove in {x : ℤ | x > 0 ∧ x < 2 * Real.pi ∧ x > 5 / 3}
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- Let's check x =2
        constructor
        · norm_num
        constructor
        · -- Check 2 < 2 * Real.pi
          have h2 : (2 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
          exact_mod_cast h2
        · -- Check 2 > 5 / 3
          norm_num
      · -- Let's check x =3
        constructor
        · norm_num
        constructor
        · -- Check 3 < 2 * Real.pi
          have h2 : (3 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
          exact_mod_cast h2
        · -- Check 3 > 5 / 3
          norm_num
      · -- Let's check x =4
        constructor
        · norm_num
        constructor
        · -- Check 4 < 2 * Real.pi
          have h2 : (4 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
          exact_mod_cast h2
        · -- Check 4 > 5 / 3
          norm_num
      · -- Let's check x =5
        constructor
        · norm_num
        constructor
        · -- Check 5 < 2 * Real.pi
          have h2 : (5 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
          exact_mod_cast h2
        · -- Check 5 > 5 / 3
          norm_num
      · -- Let's check x =6
        constructor
        · norm_num
        constructor
        · -- Check 6 < 2 * Real.pi
          have h2 : (6 : ℝ) < 2 * Real.pi := by 
            nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, Real.pi_pos]
          exact_mod_cast h2
        · -- Check 6 > 5 / 3
          norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]