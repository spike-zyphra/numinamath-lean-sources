import Mathlib

theorem algebra_2531 {x : ℝ} (hx : x = -1 / 8) : (x ^ 2) ^ ((1 : ℝ) / 3) = 1 / 4 := by
  rw [hx]
  have h1 : ((-1 / 8 : ℝ) ^ 2 : ℝ) = (1 / 64 : ℝ) := by norm_num
  rw [h1]
  have h2 : ((1 / 64 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = 1 / 4 := by
    have h3 : ((1 / 64 : ℝ) : ℝ) ^ ((1 : ℝ) / 3) = ((4 : ℝ) ^ (-3 : ℝ)) ^ ((1 : ℝ) / 3) := by
      norm_num
    rw [h3]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  exact h2