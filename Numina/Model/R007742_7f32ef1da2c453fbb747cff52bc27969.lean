import Mathlib

theorem algebra_11262 {a : ℝ} (ha : a = 50 * Real.sqrt 2) :
    Real.sqrt (a^2 + a^2) = 100 := by 
  rw [ha]
  have h2 : (50 * Real.sqrt 2 : ℝ) ^ 2 = 5000 := by
    calc
      (50 * Real.sqrt 2 : ℝ) ^ 2 = (50 ^ 2) * (Real.sqrt 2 ^ 2) := by ring
      _ = 2500 * 2 := by norm_num [Real.sq_sqrt]
      _ = 5000 := by norm_num
  have h3 : (50 * Real.sqrt 2 : ℝ) ^ 2 + (50 * Real.sqrt 2 : ℝ) ^ 2 = 10000 := by
    rw [h2]
    norm_num
  rw [h3]
  rw [Real.sqrt_eq_cases]
  all_goals norm_num