import Mathlib

theorem calculus_155861 (T : ℝ → ℝ) (hT : T = fun t => 0.2 * t ^ 2) :
    deriv T 10 = 4 := by 
  rw [hT]
  simp [deriv_const_mul, deriv_pow]
  all_goals norm_num