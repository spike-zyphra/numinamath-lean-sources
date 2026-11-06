import Mathlib

theorem algebra_231510 (x : ℝ) (hx : x = 3 - 2 * Real.sqrt 3) :
    Real.sqrt (2 * x + 1) + Real.sqrt (x + 1) = 1 := by 
  rw [hx]
  have h1 : 2 * (3 - 2 * Real.sqrt 3) + 1 = (2 - Real.sqrt 3) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h2 : (3 - 2 * Real.sqrt 3) + 1 = (Real.sqrt 3 - 1) ^ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  rw [h1, h2]
  have h3 : Real.sqrt ((2 - Real.sqrt 3) ^ 2) = abs (2 - Real.sqrt 3) := by 
    rw [Real.sqrt_sq_eq_abs]
  have h4 : Real.sqrt ((Real.sqrt 3 - 1) ^ 2) = abs (Real.sqrt 3 - 1) := by 
    rw [Real.sqrt_sq_eq_abs]
  rw [h3, h4]
  have h5 : Real.sqrt 3 < 2 := by
    have h5 : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h6 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
    linarith [h5, h6]
  have h6 : 1 < Real.sqrt 3 := by 
    have h7 : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h8 : Real.sqrt 1 = 1 := Real.sqrt_eq_cases.mpr (by norm_num)
    linarith [h7, h8]
  have h7 : abs (2 - Real.sqrt 3) = 2 - Real.sqrt 3 := by 
    rw [abs_of_pos]
    linarith
  have h8 : abs (Real.sqrt 3 - 1) = Real.sqrt 3 - 1 := by 
    rw [abs_of_pos]
    linarith
  rw [h7, h8]
  linarith