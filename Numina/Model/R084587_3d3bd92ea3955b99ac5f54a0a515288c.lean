import Mathlib

theorem algebra_146309 (x y : ℝ) (h : 4 * x + 7 * y - 3 = 0) :
    deriv (fun x => (3 - 4 * x) / 7) x < 0 := by 
  simp [deriv_const, deriv_sub, deriv_mul, deriv_id', mul_comm]
  all_goals norm_num