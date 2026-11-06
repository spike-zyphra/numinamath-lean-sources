import Mathlib

theorem calculus_155571 (f : ℝ → ℝ) (hf : f = fun x => Real.sin (x^3 - 3 * x^2)) :
    deriv f = fun x => (3 * x^2 - 6 * x) * Real.cos (x^3 - 3 * x^2) := by
  rw [hf]
  funext x
  simp [deriv_sin, deriv_sub, deriv_pow, deriv_const_mul, mul_comm]
  all_goals field_simp
  all_goals ring