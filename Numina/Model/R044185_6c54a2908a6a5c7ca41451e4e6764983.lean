import Mathlib

theorem algebra_99381 : (Real.sqrt 11 + Real.sqrt 5)^8 + (Real.sqrt 11 - Real.sqrt 5)^8 = 903712 := by
  have h1 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 11 ^ 4 = (Real.sqrt 11 ^ 2) ^ 2 := by ring
  rw [h1] at h3
  have h4 : Real.sqrt 11 ^ 4 = 121 := by nlinarith
  have h5 : Real.sqrt 11 ^ 8 = (Real.sqrt 11 ^ 4) ^ 2 := by ring
  rw [h4] at h5
  have h6 : Real.sqrt 11 ^ 8 = 14641 := by nlinarith
  have h7 : Real.sqrt 5 ^ 4 = (Real.sqrt 5 ^ 2) ^ 2 := by ring
  rw [h2] at h7
  have h8 : Real.sqrt 5 ^ 4 = 25 := by nlinarith
  have h9 : Real.sqrt 5 ^ 8 = (Real.sqrt 5 ^ 4) ^ 2 := by ring
  rw [h8] at h9
  have h10 : Real.sqrt 5 ^ 8 = 625 := by nlinarith
  nlinarith [sq_nonneg (Real.sqrt 11 ^ 2 - 11), sq_nonneg (Real.sqrt 5 ^ 2 - 5), sq_nonneg (Real.sqrt 11 * Real.sqrt 5), sq_nonneg (Real.sqrt 11 ^ 2 - Real.sqrt 5 ^ 2), sq_nonneg (Real.sqrt 11 ^ 4 - 121), sq_nonneg (Real.sqrt 5 ^ 4 - 25)]