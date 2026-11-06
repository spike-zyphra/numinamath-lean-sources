import Mathlib

theorem algebra_165400 : (Real.pi - Real.arctan (8 / 15)) / (2 * Real.arctan 4) = 1 := by
  have h1 : Real.pi - Real.arctan (8 / 15) = 2 * Real.arctan 4 := by
    have h41 : Real.arctan (4 : ℝ) > 0 := by
      have h42 : Real.arctan (4 : ℝ) > Real.arctan (0 : ℝ) := by
        apply Real.arctan_strictMono
        all_goals norm_num
      have h43 : Real.arctan (0 : ℝ) = 0 := Real.arctan_zero
      linarith
    have h42 : Real.arctan (4 : ℝ) > Real.pi / 4 := by
      have h47 : Real.arctan (1 : ℝ) = Real.pi / 4 := by
        linarith [Real.arctan_one]
      have h52 : Real.arctan (4 : ℝ) > Real.arctan (1 : ℝ) := by
        apply Real.arctan_strictMono
        all_goals norm_num
      linarith
    have h4 : Real.arctan (8 / 15) = Real.pi - 2 * Real.arctan 4 := by
      have h5 : Real.tan (Real.pi - 2 * Real.arctan 4) = (8 / 15 : ℝ) := by
        have h10 : Real.tan (2 * Real.arctan 4) = -8 / 15 := by
          have h14 : Real.tan (2 * Real.arctan 4) = 2 * (Real.tan (Real.arctan 4)) / (1 - (Real.tan (Real.arctan 4)) ^ 2) := by
            rw [Real.tan_two_mul]
          have h15 : Real.tan (Real.arctan 4) = (4 : ℝ) := Real.tan_arctan (4)
          rw [h15] at h14
          rw [h14]
          norm_num
        have h11 : Real.tan (Real.pi - 2 * Real.arctan 4) = - Real.tan (2 * Real.arctan 4) := by
          rw [Real.tan_pi_sub]
        rw [h11, h10]
        all_goals norm_num
      have h15 : Real.tan (Real.arctan (8 / 15 : ℝ)) = (8 / 15 : ℝ) := by
        rw [Real.tan_arctan]
        <;> norm_num
      have h60 : Real.arctan (Real.tan (Real.pi - 2 * Real.arctan 4)) = Real.pi - 2 * Real.arctan 4 := by
        have h125 : -(Real.pi / 2) < Real.pi - 2 * Real.arctan (4 : ℝ) := by 
          linarith [show Real.arctan (4 : ℝ) > 0 by linarith, Real.pi_pos, show Real.arctan (4 : ℝ) < Real.pi / 2 by linarith [Real.arctan_lt_pi_div_two 4, Real.pi_pos]]
        have h126 : Real.pi - 2 * Real.arctan (4 : ℝ) < Real.pi / 2 := by 
          linarith [show Real.arctan (4 : ℝ) > Real.pi / 4 by linarith [show Real.arctan (1 : ℝ) = Real.pi / 4 by linarith [Real.arctan_one], show Real.arctan (4 : ℝ) > Real.arctan (1 : ℝ) by apply Real.arctan_strictMono; all_goals norm_num], Real.pi_pos]
        have h7 : Real.arctan (Real.tan (Real.pi - 2 * Real.arctan 4)) = Real.pi - 2 * Real.arctan 4 := by
          rw [Real.arctan_tan]
          all_goals
          linarith
        exact h7
      have h70 : Real.arctan (8 / 15 : ℝ) = Real.arctan (Real.tan (Real.pi - 2 * Real.arctan 4)) := by 
        rw [show Real.tan (Real.pi - 2 * Real.arctan 4) = (8 / 15 : ℝ) by linarith [h5]]
        <;> norm_num
      rw [h60] at h70
      linarith [h70]
    linarith [h4]
  rw [h1]
  field_simp [show 2 * Real.arctan (4 : ℝ) ≠ 0 by 
    have h41 : Real.arctan (4 : ℝ) > 0 := by
      have h42 : Real.arctan (4 : ℝ) > Real.arctan (0 : ℝ) := by
        apply Real.arctan_strictMono
        all_goals norm_num
      have h43 : Real.arctan (0 : ℝ) = 0 := Real.arctan_zero
      linarith
    nlinarith
  ]
  all_goals
  nlinarith