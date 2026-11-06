import Mathlib

theorem algebra_5266 : 2017 / 2018 + Real.sqrt (((2017 ^ 2) / (2018 ^ 2)) + 2017 ^ 2 + 1) = 2018 := by 
  have h1 : Real.sqrt (((2017 ^ 2) / (2018 ^ 2)) + 2017 ^ 2 + 1) = (2017 ^ 2 + 2017 + 1) / 2018 := by 
    have h2 : (((2017 : ℝ) ^ 2) / (2018 ^ 2)) + 2017 ^ 2 + 1 = ((2017 ^ 2 + 2017 + 1) / 2018) ^ 2 := by 
      norm_num
    rw [h2]
    rw [Real.sqrt_sq]
    all_goals norm_num 
  rw [h1]
  norm_num