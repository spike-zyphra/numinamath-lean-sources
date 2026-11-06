import Mathlib

theorem inequalities_292819 (a b : ℝ) (ha : a > b) :
    (1 / 2 : ℝ)^a < (1 / 2 : ℝ)^b := by
  have h1 : (1 / 2 : ℝ) ^ a < (1 / 2 : ℝ) ^ b := by
    apply Real.rpow_lt_rpow_of_exponent_gt 
    all_goals linarith 
  linarith