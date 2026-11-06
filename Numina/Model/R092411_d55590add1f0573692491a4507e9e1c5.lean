import Mathlib

theorem calculus_155595 (x : ℝ) : deriv (fun x => (Real.cos x)^3) x = -3 * (Real.cos x)^2 * Real.sin x := by 
  -- Apply the chain rule: derivative of u^3 where u = cos(x)
  -- The derivative of u^3 is 3u^2 * u'
  -- u = cos(x), so u' = -sin(x)
  -- Therefore, derivative is 3*cos(x)^2 * (-sin(x)) = -3*cos(x)^2*sin(x)
  simp [deriv_pow, deriv_cos, mul_assoc]
  all_goals try ring_nf <;> field_simp [Real.sin_sq, Real.cos_sq]
  <;> try linarith [Real.sin_sq_add_cos_sq x]
  <;> try ring_nf <;> field_simp [Real.sin_sq, Real.cos_sq]
  <;> try linarith [Real.sin_sq_add_cos_sq x]