import Mathlib.Tactic

theorem alg_1195
  (a b c r : ℝ)
  (ha_pos : 0 < a)
  (a_ne_1 : a ≠ 1)
  (radius : r = Real.logb 10 (a ^ 2))
  (circumf : c = Real.logb 10 (b ^ 4))
  (circumf_formula : c = 2 * Real.pi * r) :
  Real.logb a b = Real.pi := by 
  have h1 : Real.logb 10 (a ^ 2) = 2 * Real.logb 10 a := by 
    simp [Real.logb_pow]
  have h2 : Real.logb 10 (b ^ 4) = 4 * Real.logb 10 b := by 
    simp [Real.logb_pow]
  rw [circumf] at circumf_formula
  rw [radius] at circumf_formula
  rw [h1] at circumf_formula
  rw [h2] at circumf_formula
  have h3 : 4 * Real.logb 10 b = 4 * Real.pi * Real.logb 10 a := by
    nlinarith
  have h4 : Real.logb 10 b = Real.pi * Real.logb 10 a := by
    nlinarith
  have h5 : Real.logb a b = Real.logb 10 b / Real.logb 10 a := by 
    field_simp [Real.logb]
  have h7 : Real.logb 10 a ≠ 0 := by 
    by_contra h
    have h8 : Real.logb 10 a = 0 := by 
      linarith 
    have h9 : a = 1 := by 
      have h9 : Real.logb 10 a = 0 := h8 
      rw [Real.logb_eq_iff_rpow_eq] at h9 
      · norm_num at h9 ⊢ 
        nlinarith 
      all_goals 
        try linarith 
        try tauto 
    contradiction
  rw [h5]
  rw [h4]
  <;> field_simp [h7] <;> nlinarith