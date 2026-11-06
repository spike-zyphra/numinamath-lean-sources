import Mathlib

theorem algebra_102907 (α β : ℝ) (h : Real.tan α + Real.tan β = 3 ∧ Real.tan α * Real.tan β = -3) :
    |Real.sin (α + β) ^ 2 - 3 * Real.sin (α + β) * Real.cos (α + β) - 3 * Real.cos (α + β) ^ 2| = 3 := by 
  rcases h with ⟨htan1, htan2⟩
  have h1 : Real.cos α ≠ 0 := by 
    by_contra h2
    have htan1' : Real.tan α = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h2]
    have htan2' : Real.tan β = 3 := by
      linarith [htan1, htan1']
    have htan2'' : Real.tan α * Real.tan β = 0 := by
      rw [htan1']
      all_goals
      nlinarith
    linarith [htan2, htan2'']
  have h2' : Real.cos β ≠ 0 := by 
    by_contra h3 
    have htan1 : Real.tan β = 0 := by 
      rw [Real.tan_eq_sin_div_cos]
      simp [h3]
    have htan1' : Real.tan α = 3 := by 
      linarith [htan1, htan1]
    have htan1'' : Real.tan α * Real.tan β = 0 := by 
      rw [htan1']
      all_goals 
      nlinarith 
    linarith [htan2, htan1'']
  have htan_add : Real.tan (α + β) = 3 / 4 := by 
    have htan_add' : Real.tan (α + β) = (Real.tan α + Real.tan β) / (1 - Real.tan α * Real.tan β) := by 
      have h1 : Real.cos α ≠ 0 := h1
      have h2 : Real.cos β ≠ 0 := h2'
      rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
      rw [Real.sin_add, Real.cos_add]
      <;> 
        field_simp [h1, h2, show Real.cos α ≠ 0 by exact h1, show Real.cos β ≠ 0 by exact h2']
        <;> 
          ring
    rw [htan_add']
    rw [htan1, htan2]
    norm_num
  have eq6 : Real.sin (α + β) ^ 2 - 3 * Real.sin (α + β) * Real.cos (α + β) - 3 * Real.cos (α + β) ^ 2 = -3 := by
    have htan_add1 : Real.tan (α + β) = 3 / 4 := htan_add
    have h7 : Real.cos (α + β) ≠ 0 := by 
      by_contra h8
      have htan_add1 : Real.tan (α + β) = 3 / 4 := htan_add
      have h0 : Real.tan (α + β) = Real.sin (α + β) / Real.cos (α + β) := by 
        rw [Real.tan_eq_sin_div_cos]
      rw [h0] at htan_add1 
      rw [h8] at htan_add1 
      norm_num [h8] at htan_add1 
      all_goals 
        all_goals 
        try { 
          have hsin_sq : Real.sin (α + β) ^ 2 = 1 := by 
            have h9 : Real.sin (α + β) ^ 2 + Real.cos (α + β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α + β)
            rw [h8] at h9 
            nlinarith 
          cases' Real.sin_eq_one_or_neg_one_of_sq_eq_one hsin_sq with hcase1 hcase2 
          · -- sin (α + β) = 1 
            rw [hcase1] at htan_add1 
            norm_num at htan_add1 
          · -- sin (α + β) = -1 
            rw [hcase2] at htan_add1 
            norm_num at htan_add1 
          all_goals 
            nlinarith 
        }
        all_goals
        try { tauto }
    have h8 : Real.tan (α + β) = Real.sin (α + β) / Real.cos (α + β) := by 
      rw [Real.tan_eq_sin_div_cos]
    have htan_add_eq : Real.sin (α + β) / Real.cos (α + β) = 3 / 4 := by 
      linarith [htan_add1, h8]
    have heq1 : Real.sin (α + β) = 3 / 4 * Real.cos (α + β) := by 
      have h8 : Real.cos (α + β) ≠ 0 := h7 
      field_simp [h8] at htan_add_eq 
      linarith 
    rw [show Real.sin (α + β) = 3 / 4 * Real.cos (α + β) by linarith [heq1]]
    have h1 : Real.cos (α + β) ^ 2 = 16 / 25 := by
      have h9 : (3 / 4 * Real.cos (α + β) ) ^ 2 + Real.cos (α + β) ^ 2 = 1 := by 
        have h0 : Real.sin (α + β) ^ 2 + Real.cos (α + β) ^ 2 = 1 := Real.sin_sq_add_cos_sq (α + β)
        rw [show Real.sin (α + β) = 3 / 4 * Real.cos (α + β) by linarith [heq1]] at h0 
        linarith 
      nlinarith 
    nlinarith [h1]
  rw [eq6]
  all_goals 
    norm_num