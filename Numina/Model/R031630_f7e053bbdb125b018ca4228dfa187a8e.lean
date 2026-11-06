import Mathlib

theorem algebra_11080 {x : ℝ} (hx : x > 0 ∧ x ≠ 1) : Real.logb x 4 = Real.logb 27 3 ↔ x = 64 := by
  constructor
  · -- Assume Real.logb x 4 = Real.logb 27 3, then prove x = 64
    intro h_eq
    have h1 : Real.logb 27 3 = 1 / 3 := by
      have h2 : Real.logb 27 3 = Real.log 3 / Real.log 27 := by 
        field_simp [Real.logb]
      have h3 : Real.log 27 = 3 * Real.log 3 := by
        rw [show (27 : ℝ) = (3 : ℝ) ^ 3 by norm_num]
        simp [Real.log_pow]
      rw [h2, h3]
      have h4 : Real.log 3 ≠ 0 := by
        have h5 : Real.log 3 > 0 := by
          apply Real.log_pos 
          all_goals norm_num
        linarith
      field_simp [h4]
      <;> linarith
    have h2 : Real.logb x 4 = 1 / 3 := by 
      linarith [h1, h_eq]
    
    have h3 : Real.logb x 4 = Real.log 4 / Real.log x := by 
      field_simp [Real.logb]
    
    rw [h3] at h2
    have h4 : Real.log 4 = 2 * Real.log 2 := by 
      calc 
        Real.log 4 = Real.log (2 ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by simp [Real.log_pow]

    rw [h4] at h2
    have h5 : Real.log 2 ≠ 0 := by
      have h6 : Real.log 2 > 0 := by
        apply Real.log_pos 
        all_goals norm_num
      linarith

    have h6 : Real.log x ≠ 0 := by
      by_contra h
      rw [h] at h2 
      norm_num [h5] at h2
    have h7 : Real.log x = 6 * Real.log 2 := by
      field_simp [h6] at h2 
      linarith

    have h6 : x = (2 : ℝ) ^ 6 := by 
      have h7' : x = Real.exp (Real.log x) := by 
        rw [Real.exp_log]
        all_goals 
          linarith [hx.1]
      rw [h7'] 
      rw [h7] 
      have h8 : Real.exp (6 * Real.log 2) = (Real.exp (Real.log 2)) ^ 6 := by 
        calc 
          Real.exp (6 * Real.log 2) = Real.exp (6 * (Real.log 2)) := by ring
          _ = (Real.exp (Real.log 2)) ^ 6 := by 
            rw [← Real.exp_nat_mul]
            <;> ring
      rw [h8]
      have h9 : Real.exp (Real.log 2) = (2 : ℝ) := by 
        rw [Real.exp_log] 
        all_goals 
          linarith
      rw [h9] 
      all_goals norm_num

    have h10 : (2 : ℝ) ^ 6 = (64 : ℝ) := by norm_num
    rw [h10] at h6
    linarith
  · -- Assume x = 64, prove Real.logb x 4 = Real.logb 27 3
    intro h_eq
    rw [h_eq]
    have h1 : Real.logb (64 : ℝ) 4 = 1 / 3 := by
      have h4 : Real.logb (64 : ℝ) 4 = Real.log 4 / Real.log (64 : ℝ) := by 
        field_simp [Real.logb]
      rw [h4]
      have h5 : Real.log 4 = 2 * Real.log 2 := by 
        calc 
          Real.log 4 = Real.log (2 ^ 2) := by norm_num
          _ = 2 * Real.log 2 := by simp [Real.log_pow]
      have h6 : Real.log (64 : ℝ) = 6 * Real.log 2 := by 
        calc
          Real.log (64 : ℝ) = Real.log (2 ^ 6) := by norm_num
          _ = 6 * Real.log 2 := by simp [Real.log_pow]
      rw [h5, h6]
      have h7 : Real.log 2 ≠ 0 := by
        have h8 : Real.log 2 > 0 := by
          apply Real.log_pos 
          all_goals norm_num
        linarith
      field_simp [h7]
      <;> ring_nf
    have h3 : Real.logb 27 3 = 1 / 3 := by
      have h2 : Real.logb 27 3 = Real.log 3 / Real.log 27 := by 
        field_simp [Real.logb]
      have h3 : Real.log 27 = 3 * Real.log 3 := by
        rw [show (27 : ℝ) = (3 : ℝ) ^ 3 by norm_num]
        simp [Real.log_pow]
      rw [h2, h3]
      have h4 : Real.log 3 ≠ 0 := by
        have h5 : Real.log 3 > 0 := by
          apply Real.log_pos 
          all_goals norm_num
        linarith
      field_simp [h4]
      <;> linarith
    linarith [h1, h3]