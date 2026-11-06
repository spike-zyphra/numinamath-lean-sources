import Mathlib

/- The derivative of the function $y=x\sin x + \cos x$ is ______. -/
theorem algebra_9379 (f : ℝ → ℝ) (hf : f = fun x => x * Real.sin x + Real.cos x) :
    deriv f = fun x => x * Real.cos x := by
  ext x
  -- Using basic manipulations of derivatives.
  rw [hf, deriv_add, deriv_mul, deriv_id'', Real.deriv_sin, Real.deriv_cos]
  simp
  -- Make sure the functions are differentiable.
  . exact differentiableAt_id
  . exact Real.differentiableAt_sin
  . exact DifferentiableAt.mul differentiableAt_id Real.differentiableAt_sin
  . exact Real.differentiableAt_cos
