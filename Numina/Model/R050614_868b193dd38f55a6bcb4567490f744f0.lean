import Mathlib

theorem algebra_14004 {x : ℝ} (hx : x > 2) (h : Real.logb 9 (x - 2) = 1 / 2) :
    Real.logb 625 x = 1 / 4 := by
  have hx_eq : x = 5 := by
    have h1 : x - 2 = (9 : ℝ) ^ (1 / 2 : ℝ) := by
      have h2_eq : Real.logb 9 (x - 2) = 1 / 2 := h
      have h3 : (x - 2 : ℝ) = (9 : ℝ) ^ (Real.logb 9 (x - 2 : ℝ) : ℝ) := by
        field_simp [Real.rpow_logb, show (9 : ℝ) > 0 by norm_num, 
          show (9 : ℝ) ≠ 1 by norm_num, 
          show (x - 2 : ℝ) > 0 by linarith]
      rw [h2_eq] at h3
      linarith
    have h2 : (9 : ℝ) ^ (1 / 2 : ℝ) = (3 : ℝ) := by
      have : (9 : ℝ) ^ (1 / 2 : ℝ) = (3 : ℝ) := by
        rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num
      linarith
    rw [h2] at h1
    linarith
  rw [hx_eq]
  have h3 : Real.logb 625 (5 : ℝ) = 1 / 4 := by
    have h625 : Real.log 625 = 4 * Real.log 5 := by
      have h625_eq : (625 : ℝ) = 5 ^ 4 := by norm_num
      rw [h625_eq]
      simp [Real.log_pow]
      all_goals linarith
      all_goals simp [Real.log_pow]
      all_goals linarith
    rw [Real.logb]
    rw [h625]
    have h5_pos : Real.log 5 ≠ 0 := by
      positivity
    field_simp [h5_pos]
    <;> ring_nf <;> norm_num
  linarith [h3]