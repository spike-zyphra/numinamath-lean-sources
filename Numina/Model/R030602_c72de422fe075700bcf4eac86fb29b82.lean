import Mathlib

open Real

theorem calculus_144515 (f : ℝ → ℝ) (hf : f = fun x => sqrt (1 + x + sin x)) (x : ℝ) (hx : x = 0.01) :
    deriv f 0 * (x - 0) + f 0 = 1.01 := by
  have h1 : f = fun x => sqrt (1 + x + sin x) := by 
    exact hf
  have h2 : f 0 = 1 := by 
    rw [h1]
    simp [sin_zero]
  have h3 : deriv f 0 = 1 := by
    rw [h1]
    simp [deriv_sqrt, deriv_add, deriv_const, add_assoc, differentiableAt_id', differentiableAt_sin]
    all_goals norm_num [sin_zero, cos_zero]
  rw [h3, h2, hx]
  all_goals norm_num