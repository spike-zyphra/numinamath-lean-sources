import Mathlib

open Real

theorem calculus_181478 {f : ℝ → ℝ} (hf : ∀ x, f x = 2^(2*x) / sqrt (2 - 2^(2*x))) :
    deriv f 0 = 3 * log 2 := by
  have f_eq : f = fun x => (2 : ℝ) ^ (2 * x) / sqrt (2 - (2 : ℝ) ^ (2 * x)) := by
    funext x
    exact hf x
  rw [f_eq]
  simp [deriv_div, deriv_pow, deriv_mul, deriv_id'', mul_comm, mul_assoc, Real.rpow_def_of_pos, 
      Real.sqrt_eq_rpow, mul_add, sub_eq_add_neg, add_left_inj]
  all_goals norm_num [Real.log_pow, mul_add, mul_assoc]
  all_goals ring_nf
  all_goals norm_num