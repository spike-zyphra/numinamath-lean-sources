import Mathlib

open Real

theorem calculus_148575 {f : ℝ → ℝ}
    (hf : f = fun x => 5^x * (2 * sin (2 * x) + cos (2 * x) * log 5) / (4 + (log 5)^2)) :
    deriv f = fun x => 5^x * cos (2 * x) := by
  rw [hf]
  funext x
  have h_deriv : deriv (fun x => (5 : ℝ) ^ x * (2 * sin (2 * x) + cos (2 * x) * log 5)) x = 
      (5 : ℝ) ^ x * (cos (2 * x) * (4 + (log 5) ^ 2)) := by
    simp [deriv_mul, deriv_pow, deriv_add, deriv_mul_const, deriv_id'', mul_comm]
    all_goals field_simp [Real.rpow_def_of_pos, Real.log_exp]
    all_goals ring_nf
    <;> simp [Real.rpow_def_of_pos, mul_comm]
    <;> ring_nf
    <;> norm_num
    <;> ring
  have h_const_denomin : (4 + log 5 ^ 2) ≠ 0 := by
    nlinarith [Real.log_pos (show (5 : ℝ) > 1 by norm_num), sq_nonneg (log 5)]
  simp [deriv_div, h_deriv, h_const_denomin]
  all_goals field_simp [h_const_denomin]
  all_goals ring_nf
  <;> norm_num
  <;> ring
  all_goals field_simp [h_const_denomin]
  all_goals linarith