import Mathlib

theorem algebra_252839 (x : ℝ) : (5 : ℝ)^(2*x-1) = (7 : ℝ)^(3-x) ↔
    x = (1 + 3 * Real.logb 5 7) / (2 + Real.logb 5 7) := by
  constructor
  · -- Assume (5 : ℝ)^(2*x-1) = (7 : ℝ)^(3-x), prove x = (1 + 3 * Real.logb 5 7) / (2 + Real.logb 5 7)
    intro h_eq
    have h2 : (2 * x - 1) * Real.log 5 = (3 - x) * Real.log 7 := by
      have h3 : Real.log ((5 : ℝ) ^ (2 * x - 1)) = Real.log ((7 : ℝ) ^ (3 - x)) := by
        rw [h_eq]
      have h4 : Real.log ((5 : ℝ) ^ (2 * x - 1)) = (2 * x - 1) * Real.log 5 := by
        rw [Real.log_rpow]
        all_goals norm_num
      have h5 : Real.log ((7 : ℝ) ^ (3 - x)) = (3 - x) * Real.log 7 := by 
        rw [Real.log_rpow]
        all_goals norm_num
      rw [h4, h5] at h3
      linarith
    have h3 : x = (1 + 3 * Real.logb 5 7) / (2 + Real.logb 5 7) := by
      have h4 : Real.log 5 ≠ 0 := by
        apply ne_of_gt
        apply Real.log_pos
        all_goals norm_num
      have h5 : Real.log 7 ≠ 0 := by
        apply ne_of_gt
        apply Real.log_pos
        all_goals norm_num
      have h6 : 2 + Real.logb 5 7 ≠ 0 := by 
        have h7 : Real.logb 5 7 > 0 := by 
          apply Real.logb_pos
          all_goals norm_num
        linarith
      have h7 : Real.logb 5 7 = Real.log 7 / Real.log 5 := by
        field_simp [Real.logb]
      field_simp [h7] at *
      ring_nf at h2 ⊢
      <;> nlinarith [h4, h5, Real.log_pos (show (5 : ℝ) > 1 by norm_num), Real.log_pos (show (7 : ℝ) > 1 by norm_num)]
    exact h3
  · -- Assume x = (1 + 3 * Real.logb 5 7) / (2 + Real.logb 5 7), prove (5 : ℝ)^(2*x-1) = (7 : ℝ)^(3-x)
    intro h_eq
    have h2 : (2 * x - 1) * Real.log 5 = (3 - x) * Real.log 7 := by
      have h3 : x = (1 + 3 * Real.logb 5 7) / (2 + Real.logb 5 7) := h_eq
      rw [h3]
      have h4 : Real.logb 5 7 ≠ 0 := by
        have h7 : Real.logb 5 7 > 0 := by 
          apply Real.logb_pos
          all_goals norm_num
        linarith
      have h5 : Real.log 5 ≠ 0 := by 
        apply ne_of_gt
        apply Real.log_pos
        all_goals norm_num
      have h6 : Real.log 7 ≠ 0 := by
        apply ne_of_gt
        apply Real.log_pos
        all_goals norm_num
      have h7 : Real.logb 5 7 = Real.log 7 / Real.log 5 := by 
        field_simp [Real.logb]
      field_simp [h7] at *
      ring_nf
      <;> nlinarith [Real.log_pos (show (5 : ℝ) > 1 by norm_num), Real.log_pos (show (7 : ℝ) > 1 by norm_num)]
    have h3 : (5 : ℝ) ^ (2 * x - 1) = (7 : ℝ) ^ (3 - x) := by
      have h4 : Real.log ((5 : ℝ) ^ (2 * x - 1)) = Real.log ((7 : ℝ) ^ (3 - x)) := by 
        have h5 : Real.log ((5 : ℝ) ^ (2 * x - 1)) = (2 * x - 1) * Real.log 5 := by 
          rw [Real.log_rpow]
          all_goals norm_num
        have h6 : Real.log ((7 : ℝ) ^ (3 - x)) = (3 - x) * Real.log 7 := by 
          rw [Real.log_rpow]
          all_goals norm_num
        rw [h5, h6]
        linarith [h2]
      have h5 : (5 : ℝ) ^ (2 * x - 1) > 0 := by positivity
      have h6 : (7 : ℝ) ^ (3 - x) > 0 := by positivity
      have h7 : (5 : ℝ) ^ (2 * x - 1) = (7 : ℝ) ^ (3 - x) := by 
        exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h4
      exact h7
    linarith [h3]