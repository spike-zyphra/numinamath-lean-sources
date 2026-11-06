import Mathlib

theorem algebra_10589 (x : ℝ) (hx : x > 0 ∧ x ≠ 1) : Real.logb x 32 = 5 / 2 ↔ x = 4 := by 
  constructor 
  · -- Assume Real.logb x 32 = 5 / 2, prove x = 4 
    intro h 
    have h1 : x ^ (5 / 2 : ℝ) = (32 : ℝ) := by
      have h2 : Real.logb x 32 = 5 / 2 := h
      have hx1 : x > (0 : ℝ) := hx.1
      have hx2 : x ≠ 1 := hx.2
      have hx3 : (32 : ℝ) > 0 := by norm_num
      rw [Real.logb_eq_iff_rpow_eq] at h2
      all_goals
        try tauto
        all_goals
          norm_num 
          <;> linarith 
    have h2 : x = 4 := by 
      have h3 : x ^ (5 / 2 : ℝ) = (32 : ℝ) := h1
      have h4 : x ^ (5 / 2 : ℝ) = (32 : ℝ) := h3 
      have h5 : x ^ (5 / 2 : ℝ) = ( (2 : ℝ) ^ (5 : ℝ) ) := by 
        rw [show (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) by norm_num] at h4 
        linarith 
      have h6 : x = (4 : ℝ) := by
        have h7 : x = (x ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by 
          rw [← Real.rpow_mul]
          norm_num 
          all_goals 
            linarith 
        rw [h5] at h7 
        have h8 : ( ( (2 : ℝ) ^ (5 : ℝ) ) ) ^ (2 / 5 : ℝ) = (4 : ℝ) := by 
          rw [← Real.rpow_mul]
          norm_num
          all_goals 
            norm_num 
        rw [h8] at h7 
        linarith 
      exact_mod_cast h6 
    exact_mod_cast h2 
  · -- Assume x = 4, prove Real.logb x 32 = 5 / 2 
    intro h 
    rw [h]
    have h6 : Real.logb (4 : ℝ) (32 : ℝ) = 5 / 2 := by 
      rw [Real.logb]
      have h7 : Real.log (32 : ℝ) = 5 * Real.log (2 : ℝ) := by 
        calc 
          Real.log (32 : ℝ) = Real.log (2 ^ 5 : ℝ) := by norm_num 
          _ = 5 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      have h8 : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by 
        calc 
          Real.log (4 : ℝ) = Real.log (2 ^ 2 : ℝ) := by norm_num
          _ = 2 * Real.log (2 : ℝ) := by simp [Real.log_pow]
      rw [h7, h8]
      have h9 : Real.log (2 : ℝ) > (0 : ℝ) := by 
        have h2_pos : (2 : ℝ) > 1 := by norm_num 
        have hne : Real.log (2 : ℝ) > 0 := by
          apply Real.log_pos 
          all_goals 
            linarith 
        linarith 
      field_simp [show Real.log (2 : ℝ) ≠ 0 by linarith]
      <;> ring 
    exact h6