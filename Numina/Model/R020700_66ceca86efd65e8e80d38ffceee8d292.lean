import Mathlib

theorem algebra_216 : (Real.sqrt (Real.sqrt 2)^5)^8 = 1024 := by
  have h1 : Real.sqrt 2 ≥ 0 := by positivity
  have h2 : Real.sqrt (Real.sqrt 2) ^ 2 = Real.sqrt 2 := Real.sq_sqrt (show 0 ≤ Real.sqrt 2 by positivity)
  have h3 : (Real.sqrt (Real.sqrt 2) ^ 5) ^ 2 = (Real.sqrt (Real.sqrt 2) ^ 2) ^ 5 := by ring
  have h4 : (Real.sqrt (Real.sqrt 2) ^ 5) ^ 2 = Real.sqrt 2 ^ 5 := by
    rw [h3, h2]
  have h5 : (Real.sqrt (Real.sqrt 2) ^ 5) ^ 8 = ((Real.sqrt (Real.sqrt 2) ^ 5) ^ 2) ^ 4 := by ring
  rw [h5, h4]
  have h6 : (Real.sqrt 2 ^ 5) ^ 4 = (Real.sqrt 2) ^ 20 := by ring
  rw [h6]
  have h7 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h8 : (Real.sqrt 2) ^ 20 = ((Real.sqrt 2) ^ 2) ^ 10 := by ring
  rw [h8, h7]
  norm_num