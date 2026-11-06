import Mathlib

open Real

theorem calculus_161953 {f : ℝ → ℝ} (hf : f = fun x => (x^2 - 2) / (x^2 + 2)) :
    deriv f = fun x => 8 * x / (x^2 + 2)^2 := by
  rw [hf]
  funext x
  simp [deriv_div, deriv_sub, deriv_add, deriv_pow, deriv_const, mul_comm]
  all_goals 
    field_simp
    ring