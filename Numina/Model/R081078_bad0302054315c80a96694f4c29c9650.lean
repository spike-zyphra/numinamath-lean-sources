import Mathlib

theorem calculus_2981 {f : ℝ → ℝ} (hf : f = fun x => (Real.exp (2 * x)) * (x ^ 3)) :
    deriv f = fun x => 2 * (Real.exp (2 * x)) * x ^ 3 + 3 * (x ^ 2) * (Real.exp (2 * x)) := by 
  rw [hf]
  funext x
  simp [deriv_mul, deriv_pow, mul_comm, mul_assoc, add_left_comm, Real.deriv_exp, mul_assoc]
  <;> field_simp
  <;> ring_nf 
  <;> field_simp
  <;> ring
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num
  <;> field_simp
  <;> ring
  all_goals norm_num
  all_goals norm_num
  all_goals norm_num
  <;> ring