import Mathlib

open Real Set

theorem inequalities_274674 :
    {p : ℕ | 0 < p ∧ -1 < sqrt p - sqrt 100 ∧ sqrt p - sqrt 100 < 1}.ncard = 39 := by 
  have h1 : {p : ℕ | 0 < p ∧ -1 < sqrt p - sqrt 100 ∧ sqrt p - sqrt 100 < 1} = Set.Icc 82 120 := by 
    ext p 
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor 
    · -- Assume p in the set
      rintro ⟨hp_pos, h1, h2⟩
      have h3 : (81 : ℝ) < (p : ℝ) := by
        have h4 : sqrt 100 = (10 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h5 : sqrt (p : ℝ) > (9 : ℝ) := by 
          nlinarith [h1, h4, Real.sqrt_nonneg (p : ℝ), Real.sqrt_nonneg 100, Real.sq_sqrt (show (0 : ℝ) ≤ (100 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (p : ℝ) by positivity)]
        have h6 : (p : ℝ) > (81 : ℝ) := by
          nlinarith [Real.sqrt_nonneg (p : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (p : ℝ) by positivity), sq_nonneg (sqrt (p : ℝ) - 9)]
        exact_mod_cast h6
      have h4 : (p : ℝ) < (121 : ℝ) := by
        have h5 : sqrt 100 = (10 : ℝ) := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h6 : sqrt (p : ℝ) < (11 : ℝ) := by 
          nlinarith [h2, h5, Real.sqrt_nonneg (p : ℝ), Real.sqrt_nonneg 100, Real.sq_sqrt (show (0 : ℝ) ≤ (p : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (100 : ℝ) by norm_num)]
        have h7 : (p : ℝ) < (121 : ℝ) := by 
          nlinarith [Real.sqrt_nonneg (p : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (p : ℝ) by positivity), sq_nonneg (sqrt (p : ℝ) - 11)]
        exact_mod_cast h7
      have hp1 : p > 81 := by 
        by_contra h 
        push_neg at h 
        have h8 : p ≤ 81 := by linarith 
        have h9 : (p : ℝ) ≤ (81 : ℝ) := by exact_mod_cast h8
        linarith 
      have hp2 : p < 121 := by 
        by_contra h 
        push_neg at h 
        have h8 : p ≥ 121 := by linarith 
        have h9 : (p : ℝ) ≥ (121 : ℝ) := by exact_mod_cast h8 
        linarith 
      constructor 
      · -- Show that 82 ≤ p
        omega 
      · -- Show that p ≤ 120 
        omega 
    · -- Assume p in [82, 120]
      rintro ⟨h3, h4⟩
      have hp_pos : p > 0 := by omega
      constructor 
      · exact hp_pos 
      constructor 
      · -- Show -1 < sqrt p - sqrt 100
        have h8 : sqrt 100 = (10 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        have h90 : sqrt (p : ℝ) > (9 : ℝ) := by 
          have h91 : (p : ℝ) > (81 : ℝ) := by 
            have hp2 : p ≥ 82 := by omega 
            have : (p : ℝ) ≥ (82 : ℝ) := by exact_mod_cast hp2 
            nlinarith 
          have h92 : sqrt (p : ℝ) = Real.sqrt (p : ℝ) := by rfl 
          have h93 : Real.sqrt (p : ℝ) > Real.sqrt (81 : ℝ) := by 
            apply Real.sqrt_lt_sqrt 
            all_goals nlinarith 
          have h94 : Real.sqrt (81 : ℝ) = (9 : ℝ) := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
          nlinarith [h93, h94] 
        nlinarith [h8, h90, Real.sqrt_nonneg (p : ℝ), Real.sqrt_nonneg 100, Real.sq_sqrt (show (0 : ℝ) ≤ (p : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (100 : ℝ) by norm_num)]
      · -- Show sqrt p - sqrt 100 < 1
        have h8 : sqrt 100 = (10 : ℝ) := by 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
        have h14 : sqrt (p : ℝ) < (11 : ℝ) := by 
          have h15 : (p : ℝ) < (121 : ℝ) := by 
            have hp2 : p ≤ 120 := by linarith 
            have : (p : ℝ) ≤ (120 : ℝ) := by exact_mod_cast hp2 
            nlinarith 
          have h16 : sqrt (p : ℝ) = Real.sqrt (p : ℝ) := by rfl 
          have h17 : Real.sqrt (p : ℝ) < Real.sqrt (121 : ℝ) := by 
            apply Real.sqrt_lt_sqrt 
            all_goals nlinarith 
          have h18 : Real.sqrt (121 : ℝ) = (11 : ℝ) := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
          nlinarith [h17, h18] 
        nlinarith [h8, h14, Real.sqrt_nonneg (p : ℝ), Real.sqrt_nonneg 100, Real.sq_sqrt (show (0 : ℝ) ≤ (p : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (100 : ℝ) by norm_num)]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp