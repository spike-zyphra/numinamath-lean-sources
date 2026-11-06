import Mathlib

/- Given the function $f(x) = e^x \sin x$, find the derivative $f'(x)$.-/
theorem algebra_9193 {f : ℝ → ℝ} (hf : f = fun x => Real.exp x * Real.sin x) :
    deriv f = fun x => Real.exp x * (Real.sin x + Real.cos x) := by
  --   [Analysis]
  -- This problem primarily tests the rules of derivatives for functions. We will use the product rule to solve it.
  -- [Step-by-Step Solution]
  -- 1. Identify the given function: $f(x) = e^x \sin x$.
  -- 2. Apply the product rule for derivatives: $(uv)' = u'v + uv'$. Here, let $u = e^x$ and $v = \sin x$.
  -- 3. Compute the derivatives of $u$ and $v$:
  --    - $u' = (e^x)' = e^x$
  --    - $v' = (\sin x)' = \cos x$
  -- 4. Substitute $u'$, $v'$, $u$, and $v$ into the product rule formula:
  --    $f'(x) = u'v + uv' = e^x \sin x + e^x \cos x$
  -- 5. Factor out the common term $e^x$ from the expression:
  --    $f'(x) = e^x (\sin x + \cos x)$
  -- So the answer is $\boxed{e^x (\sin x + \cos x)}$.
  ext x
  rw [hf, deriv_mul, Real.deriv_exp, Real.deriv_sin]
  ring
  . exact Real.differentiableAt_exp
  . exact Real.differentiableAt_sin
