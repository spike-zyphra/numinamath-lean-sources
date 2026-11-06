import Mathlib

open Real

theorem calculus_155830 (a b : ℝ → ℝ) (ha : a = fun t => 2 * t + 1) (hb : b = fun t => 3 * t + 2)
    (S : ℝ → ℝ) (hS : S = fun t => a t * b t) :
    deriv S 4 = 55 := by
  rw [hS]
  rw [ha, hb]
  simp [deriv_mul, deriv_add, deriv_const, deriv_id', mul_comm]
  all_goals norm_num