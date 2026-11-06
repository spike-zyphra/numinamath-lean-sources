import Mathlib

open Real

theorem algebra_142578 : (sin (38 * π / 3))^5 / 4^(logb 2 3 - logb 16 256) = sqrt 3 / 2 := by
  have h1 : sin (38 * π / 3) = Real.sqrt 3 / 2 := by
    have h1 : 38 * π / 3 = 12 * π + (2 * π / 3) := by 
      linarith [Real.pi_pos]
    rw [h1]
    have h2 : sin (12 * π + (2 * π / 3)) = sin (2 * π / 3) := by 
      have h3 : sin (12 * π + (2 * π / 3)) = sin (2 * π / 3) := by 
        have h2 : 12 * π + (2 * π / 3) = (2 * π / 3 : ℝ) + 6 * (2 * π) := by 
          linarith [Real.pi_pos]
        rw [h2]
        have h5 : sin ((2 * π / 3 : ℝ) + 6 * (2 * π)) = sin (2 * π / 3 : ℝ) := by 
          have h6 : sin ((2 * π / 3 : ℝ) + 6 * (2 * π)) = sin (2 * π / 3 : ℝ) := by 
            have h7 : (2 * π / 3 : ℝ) + 6 * (2 * π) = (2 * π / 3 : ℝ) + (6 * (2 * π) : ℝ) := by ring
            rw [h7]
            have h8 : sin ((2 * π / 3 : ℝ) + (6 * (2 * π) : ℝ)) = sin (2 * π / 3 : ℝ) := by 
              have h9 : sin ((2 * π / 3 : ℝ) + (6 * (2 * π) : ℝ)) = sin (2 * π / 3 : ℝ) := by 
                have h10 : 6 * (2 * π) = (6 : ℕ) * (2 * π) := by ring
                rw [h10]
                rw [Real.sin_add_nat_mul_two_pi]
              linarith
            linarith
          linarith
        linarith
      linarith
    rw [h2]
    have h3 : sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      have h4 : 2 * π / 3 = π - (π / 3) := by 
        ring
      rw [h4]
      rw [sin_pi_sub]
      have h5 : sin (π / 3) = Real.sqrt 3 / 2 := by
        exact sin_pi_div_three
      linarith
    linarith
  have h2 : (logb 16 256 : ℝ) = 2 := by 
    rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
  have h3 : (logb 2 3 - logb 16 256 : ℝ) = logb 2 3 - 2 := by 
    rw [h2]
  have h4 : (4 : ℝ) ^ (logb 2 3 - logb 16 256) = 9 / 16 := by 
    rw [h3]
    have h5 : (4 : ℝ) ^ (logb 2 3 - 2 : ℝ) = (2 : ℝ) ^ (2 * (logb 2 3 - 2) : ℝ) := by 
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring
      all_goals norm_num
      all_goals norm_num
    rw [h5]
    have h7 : (2 * (logb 2 3 - 2) : ℝ) = 2 * (logb 2 3) - 4 := by 
      ring
    rw [h7]
    have h8 : (2 : ℝ) ^ (2 * (logb 2 3) - 4 : ℝ) = ((2 : ℝ) ^ (2 * (logb 2 3) : ℝ)) / ((2 : ℝ) ^ (4 : ℝ) ) := by 
      rw [← Real.rpow_sub]
      ring_nf
      all_goals norm_num
    rw [h8]
    have h9 : (2 : ℝ) ^ (2 * (logb 2 3) : ℝ) = (3 : ℝ) ^ 2 := by 
      have h12 : (2 : ℝ) ^ (2 * (logb 2 3) : ℝ) = ((2 : ℝ) ^ (logb 2 3 : ℝ)) ^ 2 := by 
        calc
          (2 : ℝ) ^ (2 * (logb 2 3) : ℝ) = (2 : ℝ) ^ (2 * (logb 2 3) : ℝ) := by rfl
          _ = ((2 : ℝ) ^ (logb 2 3 : ℝ)) ^ 2 := by 
            rw [← Real.rpow_natCast, ← Real.rpow_mul]
            ring
            all_goals norm_num
      have h11 : (2 : ℝ) ^ (logb 2 3 : ℝ) = (3 : ℝ) := by 
        field_simp [Real.rpow_logb]
      rw [h11] at h12
      linarith
    rw [h9]
    norm_num
  rw [h1, h4]
  have h12 : (Real.sqrt 3 / 2 : ℝ) ^ 5 = (Real.sqrt 3) ^ 5 / (2 ^ 5 : ℝ) := by 
    ring
  rw [h12]
  have h13 : (Real.sqrt 3 : ℝ) ^ 5 = 9 * (Real.sqrt 3 : ℝ) := by 
    have h14 : (Real.sqrt 3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    calc 
      (Real.sqrt 3 : ℝ) ^ 5 = (Real.sqrt 3 : ℝ) ^ 4 * (Real.sqrt 3 : ℝ) := by ring
      _ = ((Real.sqrt 3 : ℝ) ^ 2) ^ 2 * (Real.sqrt 3 : ℝ) := by ring
      _ = (3 : ℝ) ^ 2 * (Real.sqrt 3 : ℝ) := by rw [h14]
      _ = (9 : ℝ) * (Real.sqrt 3 : ℝ) := by norm_num
  rw [h13]
  field_simp
  <;> nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 3 by norm_num : (3: ℝ) > 0), Real.sq_sqrt (show (0: ℝ) ≤ (3: ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - 1)]