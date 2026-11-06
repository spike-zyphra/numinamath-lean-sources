import Mathlib

theorem number_theory_96485 : {x : ℕ | x > 0 ∧ x < Real.sqrt 80 ∧ x > Real.sqrt 8}.encard = 6 := by
  have h3 : {x : ℕ | x > 0 ∧ x < Real.sqrt 80 ∧ x > Real.sqrt 8} = {3, 4, 5, 6, 7, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x in left side
      rintro ⟨hx1, hx2, hx3⟩
      have h4 : (x : ℝ) > (0 : ℝ) := by
        exact_mod_cast hx1
      have h5 : (x : ℝ) < Real.sqrt 80 := by
        exact_mod_cast hx2
      have h6 : (x : ℝ) > Real.sqrt 8 := by
        exact_mod_cast hx3
      have h7 : x ≥ 3 := by
        by_contra h
        push_neg at h
        have h8 : x ≤ 2 := by
          omega
        have h9 : (x : ℝ) ≤ (2 : ℝ) := by
          exact_mod_cast h8
        nlinarith [Real.sqrt_nonneg 8, Real.sqrt_nonneg 80, Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (80 : ℝ) ≥ 0 by norm_num), Real.sqrt_le_sqrt (show (8 : ℝ) ≤ (80 : ℝ) by norm_num)]
      have h10 : x ≤ 8 := by
        by_contra h
        push_neg at h
        have h11 : x ≥ 9 := by
          omega
        have h12 : (x : ℝ) ≥ (9 : ℝ) := by
          exact_mod_cast h11
        nlinarith [Real.sqrt_nonneg 8, Real.sqrt_nonneg 80, Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (80 : ℝ) ≥ 0 by norm_num), Real.sqrt_le_sqrt (show (8 : ℝ) ≤ (80 : ℝ) by norm_num)]
      interval_cases x <;> norm_num at *
      <;> norm_num [Real.sqrt_le_sqrt] at h5 h6 ⊢ <;> tauto
    · -- Assume x in right side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 3
        refine ⟨by norm_num, ?_, ?_⟩
        · -- Show 3 < Real.sqrt 80
          have h8 : Real.sqrt 80 > (3 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (80 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h8
        · -- Show 3 > Real.sqrt 8
          have h7 : Real.sqrt 8 < (3 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h7
      · -- x = 4
        refine ⟨by norm_num, ?_, ?_⟩
        · -- Show 4 < Real.sqrt 80
          have h8 : Real.sqrt 80 > (4 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (80 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h8
        · -- Show 4 > Real.sqrt 8
          have h7 : Real.sqrt 8 < (4 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h7
      · -- x = 5
        refine ⟨by norm_num, ?_, ?_⟩
        · -- Show 5 < Real.sqrt 80
          have h8 : Real.sqrt 80 > (5 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (80 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h8
        · -- Show 5 > Real.sqrt 8
          have h7 : Real.sqrt 8 < (5 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h7
      · -- x = 6
        refine ⟨by norm_num, ?_, ?_⟩
        · -- Show 6 < Real.sqrt 80
          have h8 : Real.sqrt 80 > (6 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (80 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h8
        · -- Show 6 > Real.sqrt 8
          have h7 : Real.sqrt 8 < (6 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h7
      · -- x = 7
        refine ⟨by norm_num, ?_, ?_⟩
        · -- Show 7 < Real.sqrt 80
          have h8 : Real.sqrt 80 > (7 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (80 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h8
        · -- Show 7 > Real.sqrt 8
          have h7 : Real.sqrt 8 < (7 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h7
      · -- x = 8
        refine ⟨by norm_num, ?_, ?_⟩
        · -- Show 8 < Real.sqrt 80
          have h8 : Real.sqrt 80 > (8 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 80, Real.sq_sqrt (show (80 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h8
        · -- Show 8 > Real.sqrt 8
          have h7 : Real.sqrt 8 < (8 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 8, Real.sq_sqrt (show (8 : ℝ) ≥ 0 by norm_num)]
          exact_mod_cast h7
  rw [h3]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl