import Mathlib

open Real

theorem calculus_127090 {f : ℝ → ℝ}
    (hf : f = fun x => (sinh x) / (2 * (cosh x)^2) + (arctan (sinh x)) / 2) :
    deriv f = fun x => 1 / (cosh x)^3 := by
  rw [hf]
  funext x
  simp [deriv_add, deriv_div, deriv_pow, Real.deriv_sinh, Real.deriv_cosh, mul_comm, Real.deriv_arctan, mul_assoc]
  have h1 : cosh x > 0 := Real.cosh_pos x
  field_simp [Real.cosh_pos x, Real.sinh_sq x]
  ring_nf
  <;> simp [Real.sinh_sq x]
  all_goals ring