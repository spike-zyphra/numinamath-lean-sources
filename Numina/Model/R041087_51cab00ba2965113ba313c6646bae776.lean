import Mathlib

theorem algebra_144615 (x : ℝ) (h : (1 / 3 : ℝ) ^ (2 * x + 5) = Real.sqrt (9 ^ (6 * x - 3))) :
    x = -1 / 4 := by
  have h1 : (1 / 3 : ℝ) ^ (2 * x + 5) = 3 ^ (- (2 * x + 5)) := by 
    rw [show (1 / 3 : ℝ) = (3 : ℝ) ^ (-1 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith 
  have h2 : Real.sqrt (9 ^ (6 * x - 3)) = (3 : ℝ) ^ (6 * x - 3) := by 
    have h3 : Real.sqrt (9 ^ (6 * x - 3)) = ((9 : ℝ) ^ (6 * x - 3)) ^ (1 / 2 : ℝ) := by 
      rw [Real.sqrt_eq_rpow]
    rw [h3]
    have h4 : ((9 : ℝ) ^ (6 * x - 3)) ^ (1 / 2 : ℝ) = ((3 : ℝ) ^ (2 * (6 * x - 3))) ^ (1 / 2 : ℝ) := by 
      have h5 : (9 : ℝ) ^ (6 * x - 3) = (3 : ℝ) ^ (2 * (6 * x - 3)) := by 
        rw [show (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) by norm_num]
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith 
      rw [h5]
    rw [h4]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith 
  rw [h1, h2] at h 
  have h3 : - (2 * x + 5) = (6 * x - 3 : ℝ) := by 
    apply_fun (Real.logb (3 : ℝ)) at h 
    have h4 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (- (2 * x + 5) : ℝ)) = (- (2 * x + 5) : ℝ) := by 
      rw [Real.logb_rpow]
      all_goals linarith 
    have h5 : Real.logb (3 : ℝ) ((3 : ℝ) ^ (6 * x - 3 : ℝ)) = (6 * x - 3 : ℝ) := by 
      rw [Real.logb_rpow]
      all_goals linarith 
    rw [h4, h5] at h 
    linarith 
  linarith 
  all_goals linarith