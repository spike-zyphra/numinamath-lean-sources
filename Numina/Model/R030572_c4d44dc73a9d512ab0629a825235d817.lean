import Mathlib

open Real

theorem algebra_184653 {x : ℝ} (hx : x > 0) :
    4 * logb 4 x + 3 = 2 * logb x 2 ↔ x = sqrt 2 ∨ x = 1 / 4 := by
  constructor
  · -- Assume the equation holds, prove $x = \sqrt{2}$ or $x = 1/4$.
    intro h_eq
    have h1 : logb 4 x = logb 2 x / 2 := by
      have h2 : logb 4 x = logb 2 x / logb 2 (4:ℝ) := by
        field_simp [logb]
      have h3 : logb 2 (4:ℝ) = 2 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h2, h3]
      all_goals linarith
    have h2 : logb x 2 = 1 / logb 2 x := by 
      have h3 : logb x 2 = logb 2 2 / logb 2 x := by 
        field_simp [logb]
        all_goals linarith
      have h4 : logb 2 2 = 1 := by 
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      rw [h3, h4]
      all_goals norm_num
      <;> linarith
    rw [h1, h2] at h_eq
    by_cases h3 : logb 2 x = 0
    · -- If logb 2 x = 0, then x = 1, which leads to a contradiction
      have h4 : x = 1 := by 
        rw [logb_eq_iff_rpow_eq] at h3
        · -- Show that x = 1
          linarith
        all_goals linarith
      rw [h4] at h_eq
      norm_num [logb_one] at h_eq
      all_goals norm_num at h_eq
    · -- Now h3 : logb 2 x ≠ 0
      have h4 : 2 * (logb 2 x) ^ 2 + 3 * (logb 2 x) - 2 = 0 := by
        field_simp [h3] at h_eq
        nlinarith
      have h5 : (logb 2 x - 1 / 2) * (logb 2 x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- logb 2 x = 1/2
        have h8 : logb 2 x = 1 / 2 := by linarith
        have h9 : x = (2 : ℝ) ^ (1 / 2 : ℝ) := by 
          rw [logb_eq_iff_rpow_eq] at h8
          · -- Show x = 2 ^ (1 / 2)
            linarith
          all_goals linarith
        have h10 : x = Real.sqrt 2 := by
          rw [h9]
          rw [Real.sqrt_eq_rpow]
        left
        exact h10
      · -- logb 2 x = -2
        have h8 : logb 2 x = -2 := by linarith
        have h9 : x = (2 : ℝ) ^ (-2 : ℝ) := by
          rw [logb_eq_iff_rpow_eq] at h8
          · -- Show x = 2 ^ (-2)
            linarith
          all_goals linarith
        have h10 : x = (1 / 4 : ℝ) := by
          rw [h9]
          norm_num
        right
        linarith
  · -- Assume $x = \sqrt{2}$ or $x = 1/4$, prove the equation.
    rintro (h_eq | h_eq)
    · -- x = sqrt 2
      rw [h_eq]
      have h1 : logb 4 (Real.sqrt 2) = 1 / 4 := by
        have h2 : logb 4 (Real.sqrt 2) = logb 2 (Real.sqrt 2) / logb 2 (4:ℝ) := by
          field_simp [logb]
        have h3 : logb 2 (4:ℝ) = 2 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
          <;> norm_num
        have h4 : logb 2 (Real.sqrt 2) = 1 / 2 := by 
          rw [Real.sqrt_eq_rpow]
          rw [logb_rpow_eq_mul_logb_of_pos]
          norm_num
          all_goals norm_num
          all_goals norm_num
        rw [h2, h3, h4]
        all_goals norm_num
      have h2 : logb (Real.sqrt 2) 2 = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
        <;> norm_num [Real.sqrt_eq_rpow]
        <;> norm_num
      rw [h1, h2]
      all_goals norm_num
    · -- x = 1/4
      rw [h_eq]
      have h1 : logb 4 (1 / 4 : ℝ) = -1 := by 
        rw [logb_eq_iff_rpow_eq] <;> norm_num
        <;> norm_num
      have h2 : logb (1 / 4 : ℝ) 2 = -1 / 2 := by
        have h3 : logb (1 / 4 : ℝ) 2 = logb 2 2 / logb 2 (1 / 4 : ℝ) := by 
          field_simp [logb]
          all_goals norm_num
        have h4 : logb 2 2 = 1 := by 
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        have h5 : logb 2 (1 / 4 : ℝ) = -2 := by 
          rw [logb_eq_iff_rpow_eq] <;> norm_num
          <;> norm_num
        rw [h3, h4, h5]
        all_goals norm_num
      rw [h1, h2]
      all_goals norm_num