import Mathlib

open Real

theorem calculus_131241 {f : ℝ → ℝ} (hf : f = fun x => 2^x * (sin x + cos x * log 2) / (1 + (log 2)^2)) :
    deriv f = fun x => 2^x * cos x := by 
  rw [hf]
  funext x
  simp [deriv_div_const, deriv_mul, deriv_add, deriv_sub, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num), mul_comm (2^x : ℝ), mul_add, add_mul, mul_assoc, mul_comm (Real.log 2 : ℝ), mul_left_comm (Real.log 2 : ℝ)]
  <;> ring_nf
  <;> norm_num [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num)]
  <;> ring_nf
  <;> field_simp [Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num)]
  <;> ring