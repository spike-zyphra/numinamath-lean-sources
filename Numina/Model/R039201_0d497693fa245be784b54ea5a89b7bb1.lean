import Mathlib

theorem algebra_19907 :
  ∏ᶠ c ∈ {c : ℤ | 0 < c ∧ ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ 3 * x1 ^ 2 + 7 * x1 + c = 0 ∧ 3 * x2 ^ 2 + 7 * x2 + c = 0}, c = 24 := by
  have h1 : {c : ℤ | 0 < c ∧ ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ 3 * x1 ^ 2 + 7 * x1 + c = 0 ∧ 3 * x2 ^ 2 + 7 * x2 + c = 0} = {1, 2, 3, 4} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume c is in the left side set, prove it is in {1,2,3,4}
      rintro ⟨hc_pos, x1, x2, hne, heq1, heq2⟩
      have h1 : (49 : ℝ) - 12 * (c : ℝ) > 0 := by
        nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by
          intro h'
          apply hne
          linarith
        ), sq_nonneg (x1 - x2), sq_nonneg (3 * x1 + 7 / 2), sq_nonneg (3 * x2 + 7 / 2),
                  sq_nonneg (x1 - x2)]
      have h2 : c < 5 := by
        by_contra h
        push_neg at h
        have h3 : (c : ℝ) ≥ (5 : ℝ) := by
          exact_mod_cast (show (c : ℤ) ≥ 5 by omega)
        nlinarith
      have h3 : c > 0 := hc_pos
      interval_cases c <;> norm_num at *
    · -- Assume c in {1,2,3,4}, prove it is in the left side set
      rintro (rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · -- Let c = 1, show exists two distinct real roots
          use (-7 + Real.sqrt 37) / 6, (-7 - Real.sqrt 37) / 6
          constructor
          · -- Show x1 ≠ x2
            by_contra h
            have h1 : (-7 + Real.sqrt 37 : ℝ) / 6 = (-7 - Real.sqrt 37 : ℝ) / 6 := by linarith
            have h2 : Real.sqrt 37 = 0 := by linarith
            have h3 : Real.sqrt 37 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 37 by norm_num)
            linarith
          constructor
          · -- Show 3 * x1 ^ 2 + 7 * x1 + 1 = 0
            field_simp
            nlinarith [Real.sqrt_nonneg 37, Real.sq_sqrt (show (0 : ℝ) ≤ 37 by norm_num)]
          · -- Show 3 * x2 ^ 2 + 7 * x2 + 1 = 0
            field_simp
            nlinarith [Real.sqrt_nonneg 37, Real.sq_sqrt (show (0 : ℝ) ≤ 37 by norm_num)]
      · constructor
        · norm_num
        · -- Let c = 2, show exists two distinct real roots
          use (-7 + Real.sqrt 25) / 6, (-7 - Real.sqrt 25) / 6
          constructor
          · -- Show x1 ≠ x2
            by_contra h
            have h1 : (-7 + Real.sqrt 25 : ℝ) / 6 = (-7 - Real.sqrt 25 : ℝ) / 6 := by linarith
            have h1' : Real.sqrt (25 : ℝ) = 5 := by
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            rw [h1'] at h1
            linarith
          constructor
          · -- Show 3 * x1 ^ 2 + 7 * x1 + 2 = 0
            field_simp
            nlinarith [Real.sqrt_nonneg 25, Real.sq_sqrt (show (0 : ℝ) ≤ 25 by norm_num)]
          · -- Show 3 * x2 ^ 2 + 7 * x2 + 2 = 0
            field_simp
            nlinarith [Real.sqrt_nonneg 25, Real.sq_sqrt (show (0 : ℝ) ≤ 25 by norm_num)]
      · constructor
        · norm_num
        · -- Let c = 3, show exists two distinct real roots
          use (-7 + Real.sqrt 13) / 6, (-7 - Real.sqrt 13) / 6
          constructor
          · -- Show x1 ≠ x2
            by_contra h
            have h1 : (-7 + Real.sqrt 13 : ℝ) / 6 = (-7 - Real.sqrt 13 : ℝ) / 6 := by linarith
            have h2 : Real.sqrt 13 = 0 := by linarith
            have h3 : Real.sqrt 13 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < 13 by norm_num)
            linarith
          constructor
          · -- Show 3 * x1 ^ 2 + 7 * x1 + 3 = 0
            field_simp
            nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
          · -- Show 3 * x2 ^ 2 + 7 * x2 + 3 = 0
            field_simp
            nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]
      · constructor
        · norm_num
        · -- Let c = 4, show exists two distinct real roots
          use (-7 + Real.sqrt 1) / 6, (-7 - Real.sqrt 1) / 6
          constructor
          · -- Show x1 ≠ x2
            by_contra h
            have h1 : (-7 + Real.sqrt 1 : ℝ) / 6 = (-7 - Real.sqrt 1 : ℝ) / 6 := by linarith
            have h1' : Real.sqrt (1 : ℝ) = 1 := by 
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
            rw [h1'] at h1
            linarith
          constructor
          · -- Show 3 * x1 ^ 2 + 7 * x1 + 4 = 0
            field_simp
            nlinarith [Real.sqrt_nonneg 1, Real.sq_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
          · -- Show 3 * x2 ^ 2 + 7 * x2 + 4 = 0
            field_simp
            nlinarith [Real.sqrt_nonneg 1, Real.sq_sqrt (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [h1]
  rw [finprod_mem_insert, finprod_mem_insert, finprod_mem_insert, finprod_mem_singleton]
  all_goals norm_num