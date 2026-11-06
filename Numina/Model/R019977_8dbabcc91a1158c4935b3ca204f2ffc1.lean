import Mathlib

open Real

theorem calculus_229003 (a : ℝ) (ha : 0 < a) (x : ℝ) :
    deriv (fun x => a ^ x) x = a ^ x * log a := by
  simp [Real.rpow_def_of_pos, ha, deriv_pow, deriv_mul, deriv_id'', mul_comm]
  <;> all_goals field_simp
  <;> try simp [Real.rpow_def_of_pos ha]
  all_goals ring_nf <;> field_simp 
  <;> try simp [Real.rpow_def_of_pos ha]
  <;> try norm_num at *
  all_goals try linarith
  all_goals try tauto
  all_goals try ring
  all_goals try linarith
  all_goals try tauto
  all_goals try ring
  all_goals try linarith
  all_goals try tauto
  all_goals try ring
  all_goals try linarith
  all_goals try tauto