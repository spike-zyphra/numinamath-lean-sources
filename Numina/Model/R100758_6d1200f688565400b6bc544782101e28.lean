import Mathlib

theorem algebra_14091 : (16 : ℝ) ^ ((7 : ℝ) / 4) = 128 := by
  have h1 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
  rw [h1]
  -- Now we need to compute ((2: ℝ) ^ (4: ℝ)) ^ (7 / 4: ℝ)
  -- Using the property (a^b)^c = a^(b*c) when a > 0
  have h2 : ((2 : ℝ) ^ (4 : ℝ)) ^ ((7 : ℝ) / 4) = (2 : ℝ) ^ (4 * (7 / 4 : ℝ)) := by 
    rw [← Real.rpow_mul]
    norm_num
    all_goals linarith
  rw [h2]
  -- Compute 4 * (7 / 4) = 7
  -- So we have 2^7
  norm_num
  all_goals norm_num