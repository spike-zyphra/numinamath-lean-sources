import Mathlib

theorem number_theory_29313 : {n : ℤ | n > (5 / 3 : ℝ) ∧ n < (2 * Real.pi : ℝ)}.encard = 5 := by
  have h1 : {n : ℤ | n > (5 / 3 : ℝ) ∧ n < (2 * Real.pi : ℝ)} = {2, 3, 4, 5, 6} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
              Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is in the set {n : ℤ | n > (5 / 3 : ℝ) ∧ n < (2 * Real.pi : ℝ)}
      intro hn
      rcases hn with ⟨h1, h2⟩
      have h3 : n ≥ 2 := by
        by_contra h
        push_neg at h
        have h4 : n ≤ 1 := by omega
        have h5 : (n : ℝ) ≤ (1 : ℝ) := by exact_mod_cast h4
        nlinarith
      have h4 : n ≤ 6 := by
        by_contra h
        push_neg at h
        have h6 : n ≥ 7 := by omega
        have h7 : (n : ℝ) ≥ (7 : ℝ) := by exact_mod_cast h6
        have h8 : (2 * Real.pi : ℝ) < (7 : ℝ) := by
          have hpi : Real.pi < 3.15 := by
            linarith [Real.pi_lt_315]
          nlinarith
        linarith
      interval_cases n <;> tauto
    · -- Assume n is in {2, 3, 4, 5, 6}
      rintro (rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · -- Show 2 < 2π
          have h1 : (2 : ℝ) < (2 * Real.pi : ℝ) := by
            have hpi : Real.pi > 3.14 := by
              linarith [Real.pi_gt_314]
            nlinarith
          norm_num at h1 ⊢
          linarith
      · constructor
        · norm_num
        · -- Show 3 < 2π
          have h1 : (3 : ℝ) < (2 * Real.pi : ℝ) := by
            have hpi : Real.pi > 3.14 := by
              linarith [Real.pi_gt_314]
            nlinarith
          norm_num at h1 ⊢
          linarith
      · constructor
        · norm_num
        · -- Show 4 < 2π
          have h1 : (4 : ℝ) < (2 * Real.pi : ℝ) := by
            have hpi : Real.pi > 3.14 := by
              linarith [Real.pi_gt_314]
            nlinarith
          norm_num at h1 ⊢
          linarith
      · constructor
        · norm_num
        · -- Show 5 < 2π
          have h1 : (5 : ℝ) < (2 * Real.pi : ℝ) := by
            have hpi : Real.pi > 3.14 := by
              linarith [Real.pi_gt_314]
            nlinarith
          norm_num at h1 ⊢
          linarith
      · constructor
        · norm_num
        · -- Show 6 < 2π
          have h1 : (6 : ℝ) < (2 * Real.pi : ℝ) := by
            have hpi : Real.pi > 3.14 := by
              linarith [Real.pi_gt_314]
            nlinarith
          norm_num at h1 ⊢
          linarith
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { native_decide }