import Mathlib

theorem algebra_17147 : {x : ℝ | (1 / 4 : ℝ) ^ (2 * x + 8) = (16 : ℝ) ^ (2 * x + 5)} = {-3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x is in the solution set, which means (1/4)^(2x+8) = 16^(2x+5)
    intro h
    have h1 : (1 / 4 : ℝ) ^ (2 * x + 8) = (16 : ℝ) ^ (2 * x + 5) := h
    have h2 : (1 / 4 : ℝ) ^ (2 * x + 8) = (2 : ℝ) ^ (-4 * x - 16) := by 
      rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    have h3 : (16 : ℝ) ^ (2 * x + 5) = (2 : ℝ) ^ (8 * x + 20) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h2, h3] at h1
    have h4 : -4 * x - 16 = 8 * x + 20 := by
      apply_fun (Real.logb (2 : ℝ)) at h1
      have h5 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (-4 * x - 16)) = Real.logb (2 : ℝ) ((2 : ℝ) ^ (8 * x + 20)) := by linarith [h1]
      have h6 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (-4 * x - 16)) = -4 * x - 16 := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      have h7 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (8 * x + 20)) = 8 * x + 20 := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      linarith [h5, h6, h7]
    linarith
  · -- Assume x = -3, we need to show (1/4)^(2x+8) = 16^(2x+5)
    intro h
    rw [h]
    norm_num