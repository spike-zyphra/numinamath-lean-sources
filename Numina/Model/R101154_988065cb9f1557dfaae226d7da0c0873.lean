import Mathlib

theorem calculus_155356 (f : ℝ → ℝ) (hf : f = fun x => (x ^ 2 - 2) / (x ^ 2 + 2)) :
    deriv f = fun x => 8 * x / (x ^ 2 + 2) ^ 2 := by 
  rw [hf]
  funext x
  simp [deriv_div, deriv_sub, deriv_add, deriv_pow, deriv_const, mul_comm]
  field_simp
  ring
  all_goals norm_num
  <;> ring_nf <;> field_simp <;> ring