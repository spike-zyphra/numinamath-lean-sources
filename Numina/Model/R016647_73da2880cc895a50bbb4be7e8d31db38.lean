import Mathlib

theorem algebra_269826 {a b : ℝ} (ha : a ≠ 0) (h1 : {x | x = a ∨ x = b / a ∨ x = 1} = {x | x = a ^ 2 ∨ x = a + b ∨ x = 0}) :
    a ^ 2002 + b ^ 2003 = 1 := by
  have h2 : (1 : ℝ) ∈ {x | x = a ∨ x = b / a ∨ x = 1} := by 
    simp 
  have h3 : (1 : ℝ) ∈ {x | x = a ^ 2 ∨ x = a + b ∨ x = 0} := by 
    rw [h1] at *
    exact h2 
  simp at h3 
  rcases h3 with (h4 | h5)
  · -- h4 : a ^ 2 = 1 
    have h4' : a ^ 2 = 1 := by 
      linarith 
    have h7 : a ^ 2002 + b ^ 2003 = 1 := by 
      have h9 : (0 : ℝ) ∈ {x | x = a ^ 2 ∨ x = a + b ∨ x = 0} := by 
        simp 
      have h10 : (0 : ℝ) ∈ {x | x = a ∨ x = b / a ∨ x = 1} := by 
        rw [h1] at *
        exact h9 
      simp at h10 
      rcases h10 with (h11 | h12 )
      · -- h11 : a = 0 
        exfalso 
        exact ha (by linarith)
      · -- h12 : b / a = 0 
        have h14 : b = 0 := by 
          have h15 : b / a = 0 := by linarith 
          field_simp [ha] at h15 ⊢ 
          all_goals linarith 
        have h16 : a ^ 2 = 1 := h4' 
        have h17 : a ^ 2002 = 1 := by 
          calc 
            a ^ 2002 = (a ^ 2) ^ 1001 := by ring 
            _ = 1 ^ 1001 := by rw [h16] 
            _ = 1 := by norm_num 
        rw [h17, h14] 
        all_goals norm_num 
    exact h7 
  · -- h5 : a + b = 1 
    have h12 : a + b = 1 := by 
      linarith 
    have h9 : (0 : ℝ) ∈ {x | x = a ^ 2 ∨ x = a + b ∨ x = 0} := by 
      simp 
    have h10 : (0 : ℝ) ∈ {x | x = a ∨ x = b / a ∨ x = 1} := by 
      rw [h1] at *
      exact h9 
    simp at h10 
    rcases h10 with (h11 | h12 )
    · -- h11 : a = 0 
      exfalso 
      exact ha (by linarith)
    · -- h12 : b / a = 0 
      have h14 : b = 0 := by 
        have h15 : b / a = 0 := by linarith 
        field_simp [ha] at h15 ⊢ 
        all_goals linarith 
      have h15 : a = 1 := by 
        linarith [h12, h14] 
      rw [h15, h14] 
      all_goals norm_num