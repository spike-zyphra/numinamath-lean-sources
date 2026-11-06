import Mathlib

theorem algebra_114658 {x : ℝ} (hx : x > 0 ∧ x ≠ 1) :
    Real.logb 3 x + Real.logb x 3 - 2 * Real.logb 3 x * Real.logb x 3 = 1 / 2 ↔
    x = Real.sqrt 3 ∨ x = 9 := by 
  constructor
  · -- Assume the equation holds, prove the disjunction.
    intro h_eq 
    have hx1 : x > 0 := hx.1 
    have hx2 : x ≠ 1 := hx.2 
    have h1 : Real.logb x 3 = 1 / Real.logb 3 x := by 
      field_simp [Real.logb]
    rw [h1] at h_eq 
    have h2 : Real.logb 3 x ≠ 0 := by 
      have h3 : Real.logb 3 x ≠ 0 := by
        have hx4 : x > 0 := hx1
        have hx5 : x ≠ 1 := hx2 
        have h6 : Real.logb 3 x = (Real.log x) / (Real.log (3 : ℝ)) := by 
          field_simp [Real.logb]
        rw [h6]
        have h7 : Real.log x ≠ 0 := by 
          have hx8 : x > 0 := hx1
          have hx9 : x ≠ 1 := hx2
          have h10 : Real.log x ≠ 0 := by
            have h11 : Real.log x ≠ 0 := by 
              by_contra h
              have h12 : x = 1 := by 
                rw [Real.log_eq_zero] at h 
                rcases h with (r | r | r)
                · linarith 
                · linarith 
                · linarith 
              contradiction 
            assumption
          assumption
        have h8 : Real.log (3 : ℝ) ≠ 0 := by 
          have : (3 : ℝ) > 0 := by norm_num 
          have : (3 : ℝ) ≠ 1 := by norm_num 
          have h11 : Real.log (3 : ℝ) ≠ 0 := by 
            have : (3 : ℝ) > 0 := by norm_num 
            have : (3 : ℝ) ≠ 1 := by norm_num 
            have h11 : Real.log (3 : ℝ) ≠ 0 := by 
              apply Real.log_ne_zero_of_pos_of_ne_one 
              all_goals norm_num 
            assumption 
          assumption
        field_simp [h7, h8]
      assumption 
    have h3 : Real.logb 3 x + 1 / Real.logb 3 x - 2 = 1 / 2 := by 
      field_simp [h2] at h_eq ⊢
      linarith 
    have h4 : Real.logb 3 x ^ 2 - (5 / 2) * Real.logb 3 x + 1 = 0 := by
      have h5 : Real.logb 3 x + 1 / Real.logb 3 x = 5 / 2 := by linarith 
      field_simp [h2] at h5 ⊢ 
      linarith 
    have h5 : 2 * Real.logb 3 x ^ 2 - 5 * Real.logb 3 x + 2 = 0 := by 
      linarith 
    have h6 : (2 * Real.logb 3 x - 1) * (Real.logb 3 x - 2) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h6) with h7 h8 
    · -- Case $2 * Real.logb 3 x - 1 = 0$
      have hlog1 : Real.logb 3 x = 1 / 2 := by linarith 
      have hx3 : x = Real.sqrt 3 := by 
        have h31 : Real.logb 3 x = 1 / 2 := hlog1 
        have h42 : x = (3 : ℝ) ^ (Real.logb 3 x) := by 
          field_simp 
        rw [h31] at h42 
        have h53 : x = (3 : ℝ) ^ (1 / 2 : ℝ) := by linarith 
        have h64 : (3 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 3 := by 
          rw [Real.sqrt_eq_rpow] 
        rw [h64] at h53 
        linarith 
      left 
      exact hx3 
    · -- Case $Real.logb 3 x - 2 = 0$
      have hlog2 : Real.logb 3 x = 2 := by linarith 
      have hx4 : x = 9 := by 
        have h31 : Real.logb 3 x = 2 := hlog2 
        have h42 : x = (3 : ℝ) ^ (Real.logb 3 x) := by 
          field_simp 
        rw [h31] at h42 
        have h53 : x = (3 : ℝ) ^ (2 : ℝ) := by linarith 
        norm_num at h53 ⊢ 
        linarith 
      right
      exact hx4 
  · -- Assume the disjunction, prove the equation.
    rintro (h_eq | h_eq)
    · -- h_eq means x = Real.sqrt 3
      rw [h_eq]
      have h1 : Real.logb 3 (Real.sqrt 3) = 1 / 2 := by 
        rw [Real.sqrt_eq_rpow] 
        rw [Real.logb_rpow_eq_mul_logb_of_pos]
        all_goals norm_num 
      have h2 : Real.logb (Real.sqrt 3) 3 = 2 := by 
        have h31 : Real.logb (Real.sqrt 3) 3 = Real.log 3 / Real.log (Real.sqrt 3) := by
          field_simp [Real.logb]
        rw [h31]
        have h41 : Real.log (Real.sqrt 3) = (1 / 2) * Real.log (3 : ℝ) := by 
          rw [Real.sqrt_eq_rpow] 
          rw [Real.log_rpow] 
          all_goals norm_num 
          <;> linarith 
        rw [h41] 
        field_simp 
        <;> linarith 
      rw [h1, h2]
      norm_num 
    · -- h_eq means x = 9
      rw [h_eq]
      have h1 : Real.logb 3 (9 : ℝ) = 2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      have h2 : Real.logb (9 : ℝ) 3 = 1 / 2 := by 
        have h31 : Real.logb (9 : ℝ) 3 = Real.log 3 / Real.log (9 : ℝ) := by 
          field_simp [Real.logb]
        rw [h31] 
        have h41 : Real.log (9 : ℝ) = 2 * Real.log 3 := by 
          calc 
            Real.log (9 : ℝ) = Real.log ((3 : ℝ) ^ 2) := by norm_num
            _ = 2 * Real.log (3 : ℝ) := by simp [Real.log_pow]
        rw [h41] 
        field_simp 
        all_goals linarith 
      rw [h1, h2]
      norm_num