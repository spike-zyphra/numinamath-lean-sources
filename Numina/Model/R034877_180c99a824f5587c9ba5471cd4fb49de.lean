import Mathlib

theorem algebra_16056 {b : ℝ} (hb : b > 0 ∧ b ≠ 1) (h : Real.logb b 343 = -3 / 2) :
    b = 1 / 49 := by
  have h1 : b ^ (-3 / 2 : ℝ) = 343 := by
    rw [←h]
    field_simp [Real.rpow_logb, hb.1, hb.2, show (343 : ℝ) > 0 by norm_num]
  have h2 : b ^ (3 / 2 : ℝ) = (1 / 343 : ℝ) := by
    have eq1 : b ^ (-3 / 2 : ℝ) = 343 := h1
    have eq2 : b ^ (-3 / 2 : ℝ) = (b ^ (3 / 2 : ℝ))⁻¹ := by
      rw [← Real.rpow_neg]
      ring_nf
      all_goals linarith [hb.1]
    have eq3 : (b ^ (3 / 2 : ℝ))⁻¹ = 343 := by
      linarith [eq1, eq2]
    have eq4 : b ^ (3 / 2 : ℝ) = (1 / 343 : ℝ) := by
      have h3 : b ^ (3 / 2 : ℝ) > 0 := by
        apply Real.rpow_pos_of_pos
        exact hb.1
      have eq5 : b ^ (3 / 2 : ℝ) = (1 / 343 : ℝ) := by
        have h4 : (b ^ (3 / 2 : ℝ))⁻¹ = 343 := eq3
        have h5 : b ^ (3 / 2 : ℝ) = (1 / 343 : ℝ) := by
          have h6 : ((b ^ (3 / 2 : ℝ))⁻¹)⁻¹ = (343)⁻¹ := by 
            rw [h4]
          have h7 : ((b ^ (3 / 2 : ℝ))⁻¹)⁻¹ = b ^ (3 / 2 : ℝ) := by
            have h8 : b ^ (3 / 2 : ℝ) > 0 := h3
            field_simp
          have h9 : (343 : ℝ)⁻¹ = (1 / 343 : ℝ) := by 
            norm_num
          rw [h7] at h6
          rw [h9] at h6
          linarith
        exact h5
      exact eq5
    exact eq4
  -- Now from b^(3/2) = 1/343, solve for b
  have h3 : b = ((1 / 343 : ℝ) ) ^ (2 / 3 : ℝ) := by
    have h4 : b ^ (3 / 2 : ℝ) = (1 / 343 : ℝ) := h2
    have h5 : b = (b ^ (3 / 2 : ℝ) ) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith
    rw [h4] at h5
    exact h5
  -- Now compute (1/343)^(2/3) and show it is 1/49
  have h4 : ((1 / 343 : ℝ) ) ^ (2 / 3 : ℝ) = (1 / 49 : ℝ) := by
    have h5 : ( (1 / 343 : ℝ) ) ^ (2 / 3 : ℝ) = ( ( (1 / 7 : ℝ) ^ (3 : ℝ) ) ) ^ (2 / 3 : ℝ) := by
      norm_num
    rw [h5]
    have h6 : ( ( (1 / 7 : ℝ) ^ (3 : ℝ) ) ) ^ (2 / 3 : ℝ) = ( (1 / 7 : ℝ) ) ^ (2 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    rw [h6]
    norm_num
  rw [h4] at h3
  linarith