import Mathlib

theorem algebra_21289 (x : ℝ) (h : (11 : ℝ) ^ ((3 * x - 3) / 4) = 1 / 5) :
    (11 : ℝ) ^ ((6 * x + 2) / 4) = 121 / 25 := by
  have eq1 : (11 : ℝ) ^ ((6 * x + 2) / 4) = ((11 : ℝ) ^ ((3 * x - 3) / 4 : ℝ)) ^ 2 * (11 : ℝ) ^ (2 : ℝ) := by
    have h1 : ((6 * x + 2) / 4 : ℝ) = 2 * ((3 * x - 3) / 4 : ℝ) + 2 := by
      ring_nf
    rw [h1]
    calc
      (11 : ℝ) ^ (2 * ((3 * x - 3) / 4 : ℝ) + 2) = (11 : ℝ) ^ (2 * ((3 * x - 3) / 4 : ℝ)) * (11 : ℝ) ^ (2 : ℝ) := by 
        rw [Real.rpow_add]
        all_goals linarith
      _ = ((11 : ℝ) ^ ((3 * x - 3) / 4 : ℝ)) ^ 2 * (11 : ℝ) ^ (2 : ℝ) := by 
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul]
        ring_nf
        all_goals linarith
  rw [h] at eq1
  have eq2 : ((1 / (5 : ℝ)) ^ 2) * (11 : ℝ) ^ (2 : ℝ) = (121 / 25 : ℝ) := by
    norm_num
  rw [eq2] at eq1
  linarith