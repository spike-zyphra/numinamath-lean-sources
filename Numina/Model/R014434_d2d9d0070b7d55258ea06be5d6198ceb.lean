import Mathlib

theorem algebra_96868 (x : ℝ) : (9 : ℝ)^(x + 2) = 240 + (9 : ℝ)^x ↔ x = 0.5 := by
  constructor
  · -- Assume (9 : ℝ)^(x + 2) = 240 + (9 : ℝ)^x, prove x = 0.5
    intro h
    have h1 : (9 : ℝ) ^ (x + 2) = (9 : ℝ) ^ x * (81 : ℝ) := by
      have h1 : (9 : ℝ) ^ (x + 2) = (9 : ℝ) ^ x * (9 : ℝ) ^ (2 : ℝ) := by 
        rw [← Real.rpow_add]
        ring_nf 
        all_goals linarith
      have h2 : (9 : ℝ) ^ (2 : ℝ) = (81 : ℝ) := by 
        norm_num
      rw [h1, h2]
    rw [h1] at h
    have h2 : (9 : ℝ) ^ x = (3 : ℝ) := by
      have h3 : (9 : ℝ) ^ x * (81 : ℝ) = (240 : ℝ) + (9 : ℝ) ^ x := by 
        linarith
      have h4 : (9 : ℝ) ^ x * (81 : ℝ) - (9 : ℝ) ^ x = (240 : ℝ) := by 
        linarith
      have h5 : (9 : ℝ) ^ x * (80 : ℝ) = (240 : ℝ) := by
        nlinarith [h4]
      have h6 : (9 : ℝ) ^ x = (3 : ℝ) := by
        nlinarith [h5]
      exact h6
    have h3 : x = (1 / 2 : ℝ) := by
      have h4 : (9 : ℝ) ^ x = (3 : ℝ) := h2
      have h5 : x = Real.logb (9 : ℝ) (3 : ℝ) := by 
        rw [← h4]
        field_simp [Real.rpow_pos_of_pos]
      rw [h5]
      have h6 : Real.logb (9 : ℝ) (3 : ℝ) = (Real.log (3 : ℝ) ) / (Real.log (9 : ℝ) ) := by
        field_simp [Real.logb]
        all_goals linarith
      rw [h6]
      have h7 : Real.log (9 : ℝ) = 2 * Real.log (3 : ℝ) := by
        calc 
          Real.log (9 : ℝ) = Real.log ((3 : ℝ) ^ 2) := by norm_num
          _ = 2 * Real.log (3 : ℝ) := by simp [Real.log_pow]
      rw [h7]
      have h8 : Real.log (3 : ℝ) ≠ 0 := by
        apply ne_of_gt
        apply Real.log_pos
        all_goals norm_num
      field_simp [h8]
      all_goals linarith
    have h4 : x = (0.5 : ℝ) := by
      rw [h3]
      norm_num
    exact h4
  · -- Assume x = 0.5, prove (9 : ℝ)^(x + 2) = 240 + (9 : ℝ)^x
    intro h
    rw [h]
    have h1 : (9 : ℝ) ^ ((0.5 : ℝ) + 2) = (9 : ℝ) ^ (0.5 : ℝ) * (81 : ℝ) := by
      have h1 : (9 : ℝ) ^ ((0.5 : ℝ) + 2) = (9 : ℝ) ^ (0.5 : ℝ) * (9 : ℝ) ^ (2 : ℝ) := by 
        rw [← Real.rpow_add]
        ring_nf 
        all_goals norm_num
      have h2 : (9 : ℝ) ^ (2 : ℝ) = (81 : ℝ) := by
        norm_num
      rw [h1, h2]
    have h3 : (9 : ℝ) ^ (0.5 : ℝ) = (3 : ℝ) := by
      have h4 : (9 : ℝ) ^ (0.5 : ℝ) = (3 : ℝ) := by
        rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      exact h4
    rw [h1, h3]
    all_goals norm_num