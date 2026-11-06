import Mathlib

theorem inequalities_190098 (x : ℝ) :
    (2 / 7 : ℝ) ^ (3 * (2 * x - 7)) * 12.25 ^ ((4 * x + 1) / 2) ≥ 1 ↔ x ≤ 11 := by
  constructor
  · -- Assume the inequality holds, prove x ≤ 11
    intro h
    have h1 : (2 / 7 : ℝ) ^ (3 * (2 * x - 7)) * (12.25 : ℝ) ^ ((4 * x + 1) / 2) = (2 / 7 : ℝ) ^ (2 * x - 22) := by
      have h2 : (12.25 : ℝ) ^ ((4 * x + 1) / 2) = (2 / 7 : ℝ) ^ (-4 * x -1) := by
        have h3 : (12.25 : ℝ) = (2 / 7 : ℝ) ^ (-2 : ℝ) := by norm_num
        rw [h3]
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h2]
      have h4 : (2 / 7 : ℝ) ^ (3 * (2 * x - 7)) * (2 / 7 : ℝ) ^ (-4 * x -1) = (2 / 7 : ℝ) ^ (2 * x - 22) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals norm_num
      linarith [h4]
    rw [h1] at h
    by_contra h3
    push_neg at h3
    have h3 : 2 * x - 22 > (0 : ℝ) := by linarith
    have h4 : (2 / 7 : ℝ) ^ (2 * x - 22) < (1 : ℝ) := by
      have h5 : (2 / 7 : ℝ) < (1 : ℝ) := by norm_num
      have h6 : (2 / 7 : ℝ) > (0 : ℝ) := by norm_num
      have h7 : 2 * x - 22 > (0 : ℝ) := by linarith
      have h8 : (2 / 7 : ℝ) ^ (2 * x - 22) < (2 / 7 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_gt
        all_goals linarith
      have h9 : (2 / 7 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
        simp
      linarith [h8, h9]
    linarith [h4, h]
  · -- Assume x ≤ 11, prove the inequality
    intro h
    have h1 : (2 / 7 : ℝ) ^ (3 * (2 * x - 7)) * (12.25 : ℝ) ^ ((4 * x + 1) / 2) = (2 / 7 : ℝ) ^ (2 * x - 22) := by
      have h2 : (12.25 : ℝ) ^ ((4 * x + 1) / 2) = (2 / 7 : ℝ) ^ (-4 * x -1) := by
        have h3 : (12.25 : ℝ) = (2 / 7 : ℝ) ^ (-2 : ℝ) := by norm_num
        rw [h3]
        rw [← Real.rpow_mul]
        ring_nf
        all_goals norm_num
      rw [h2]
      have h4 : (2 / 7 : ℝ) ^ (3 * (2 * x - 7)) * (2 / 7 : ℝ) ^ (-4 * x -1) = (2 / 7 : ℝ) ^ (2 * x - 22) := by
        rw [← Real.rpow_add]
        ring_nf
        all_goals norm_num
      linarith [h4]
    rw [h1]
    have h2 : (2 * x - 22 : ℝ) ≤ (0 : ℝ) := by linarith
    have h3 : (2 / 7 : ℝ) ^ (2 * x - 22) ≥ (1 : ℝ) := by
      have h4 : (2 / 7 : ℝ) < (1 : ℝ) := by norm_num
      have h5 : (2 / 7 : ℝ) > (0 : ℝ) := by norm_num
      have h6 : (2 * x - 22 : ℝ) ≤ (0 : ℝ) := h2
      have h7 : (2 / 7 : ℝ) ^ (2 * x - 22) ≥ (2 / 7 : ℝ) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_ge
        all_goals linarith
      have h8 : (2 / 7 : ℝ) ^ (0 : ℝ) = (1 : ℝ) := by
        simp
      linarith [h7, h8]
    linarith [h3]