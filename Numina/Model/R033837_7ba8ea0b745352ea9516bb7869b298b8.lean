import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_146175 {f : ℝ → ℝ} (hf : f = λ x => (sinh x) / (1 + cosh x)) :
    deriv f = λ x => 1 / (1 + cosh x) := by 
  rw [hf]
  funext x
  simp [deriv_div, differentiableAt_id', Real.differentiableAt_sinh, Real.differentiableAt_cosh,
      mul_comm]
  have h1 : cosh x + 1 = 1 + cosh x := by ring
  have h2 : cosh x ^ 2 - sinh x ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq x
  field_simp [(show 1 + cosh x ≠ 0 by 
    have h3 : cosh x ≥ 1 := Real.one_le_cosh x
    linarith
  )]
  <;> nlinarith [h2, Real.one_le_cosh x]