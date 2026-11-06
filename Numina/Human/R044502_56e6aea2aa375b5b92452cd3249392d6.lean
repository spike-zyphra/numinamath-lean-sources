import Mathlib

/- Find the derivative of the function $f(x)=2x\sin (2x+5)$. -/
theorem algebra_8989 {f : ℝ → ℝ} (hf : f = fun x => 2 * x * Real.sin (2 * x + 5)) :
  deriv f = fun x => 2 * Real.sin (2 * x + 5) + 4 * x * Real.cos (2 * x + 5) := by
    simp [hf]
    ext x
    -- To find the derivative of $f(x)=2x\sin (2x+5)$, we will use the product rule,
    -- which states that for a function $h(x)=u(x)v(x)$, the derivative is given by $h'(x)=u'(x)v(x)+u(x)v'(x)$.
    rw [deriv_mul, deriv_sin, deriv_const_mul, deriv_add, deriv_const_mul]
    -- Now, applying the product rule, we get:
    -- $f'(x)=u'(x)v(x)+u(x)v'(x)=2\sin (2x+5)+2x(2\cos (2x+5))$.
    simp
    ring
    exact differentiableAt_id'
    exact DifferentiableAt.const_mul (differentiableAt_id') 2
    exact differentiableAt_const 5
    exact differentiableAt_id'
    exact DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_id') 2)
      (differentiableAt_const 5)
    exact DifferentiableAt.const_mul (differentiableAt_id') 2
    exact DifferentiableAt.sin <| DifferentiableAt.add (DifferentiableAt.const_mul (differentiableAt_id') 2)
      (differentiableAt_const 5)
