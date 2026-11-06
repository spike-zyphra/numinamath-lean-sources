import Mathlib

def f (x : ℝ) := 5 * x ^ 2 - x + 4

theorem calculus_155321 : deriv f = fun x => 10 * x - 1 := by 
  have hf : f = fun x => 5 * x ^ 2 - x + 4 := by
    funext x 
    simp [f]

  rw [hf]
  funext x 
  simp [deriv_pow, deriv_sub, deriv_add, deriv_id'', deriv_const]
  all_goals
    norm_num [deriv_pow, deriv_sub, deriv_add, deriv_id'', deriv_const]
    all_goals ring