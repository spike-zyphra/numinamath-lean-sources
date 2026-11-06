import Mathlib

theorem algebra_240666 : √((20212020 * 20202021) - (20212021 * 20202020)) = 100 := by 
  have h1 : (20212020 * 20202021 : ℝ) - (20212021 * 20202020 : ℝ) = (10000 : ℝ) := by norm_num
  rw [h1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> norm_num
  all_goals norm_num