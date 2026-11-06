import Mathlib

open Real

theorem calculus_155537 (y : ℝ → ℝ) (hy : y = fun x => 2 ^ sin x) :
    deriv y = fun x => 2 ^ sin x * log 2 * cos x := by 
  rw [hy]
  funext x 
  simp [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num), deriv_mul, deriv_id'', mul_comm]
  all_goals norm_num [Real.log_exp, Real.rpow_pos_of_pos]
  all_goals try { field_simp [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num), Real.log_exp, Real.rpow_pos_of_pos] }
  <;> try { norm_num }
  <;> try { ring }