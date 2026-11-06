import Mathlib

open Set

theorem algebra_10990 : {x : ℤ | x > 0 ∧ 5 / 3 < x ∧ x < 2 * Real.pi}.encard = 5 := by
  have h1 : {x : ℤ | x > 0 ∧ 5 / 3 < x ∧ x < 2 * Real.pi} = {2, 3, 4, 5, 6} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n ∈ {x : ℤ | x > 0 ∧ 5 / 3 < x ∧ x < 2 * Real.pi}, prove n ∈ {2, 3, 4, 5, 6}
      intro h
      rcases h with ⟨h_pos, h1, h2⟩
      have h3 : n ≥ 2 := by
        by_contra h
        push_neg at h
        have h4 : n < 2 := by omega
        have h5 : n ≤ 1 := by omega
        have h10 : n ≤ 1 := h5
        have h11 : (n : ℝ) ≤ (1 : ℝ) := by exact_mod_cast h10
        norm_num at h1 h11
        all_goals
          nlinarith
      have h4 : n ≤ 6 := by
        by_contra h
        push_neg at h
        have h5 : n ≥ 7 := by omega
        have h6 : (n : ℝ) ≥ (7 : ℝ) := by exact_mod_cast h5
        have h7 : (2 * Real.pi : ℝ) < (7 : ℝ) := by
          linarith [Real.pi_lt_31416]
        have h12 : (n : ℝ) < (2 * Real.pi : ℝ) := by exact_mod_cast h2
        all_goals
          nlinarith [Real.pi_gt_three]
      interval_cases n <;> norm_num at *
    · -- Assume n ∈ {2, 3, 4, 5, 6}, prove n ∈ {x : ℤ | x > 0 ∧ 5 / 3 < x ∧ x < 2 * Real.pi}
      rintro (rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · -- Show that (2 : ℝ) > (5 / 3 : ℝ)
          norm_num
        · -- Show that (2 : ℝ) < (2 * Real.pi : ℝ)
          have h1 : (2 : ℝ) < (2 * Real.pi : ℝ) := by
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1
      · constructor
        · norm_num
        constructor
        · -- Show that (3 : ℝ) > (5 / 3 : ℝ)
          norm_num
        · -- Show that (3 : ℝ) < (2 * Real.pi : ℝ)
          have h1 : (3 : ℝ) < (2 * Real.pi : ℝ) := by
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1
      · constructor
        · norm_num
        constructor
        · -- Show that (4 : ℝ) > (5 / 3 : ℝ)
          norm_num
        · -- Show that (4 : ℝ) < (2 * Real.pi : ℝ)
          have h1 : (4 : ℝ) < (2 * Real.pi : ℝ) := by
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1
      · constructor
        · norm_num
        constructor
        · -- Show that (5 : ℝ) > (5 / 3 : ℝ)
          norm_num
        · -- Show that (5 : ℝ) < (2 * Real.pi : ℝ)
          have h1 : (5 : ℝ) < (2 * Real.pi : ℝ) := by
            nlinarith [Real.pi_gt_three]
          exact_mod_cast h1
      · constructor
        · norm_num
        constructor
        · -- Show that (6 : ℝ) > (5 / 3 : ℝ)
          norm_num
        · -- Show that (6 : ℝ) < (2 * Real.pi : ℝ)
          have h1 : (6 : ℝ) < (2 * Real.pi : ℝ) := by
            nlinarith [Real.pi_gt_three, Real.pi_lt_31416]
          exact_mod_cast h1
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals try { aesop }